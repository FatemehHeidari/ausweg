//! Model interface (Step 4 architecture): every stage talks to the LLM only
//! through `Model`, so swapping Ollama for a hosted tier touches this file alone.

use anyhow::{Context, Result};
use serde_json::{Value, json};
use std::time::Duration;

pub trait Model {
    /// Send one prompt, get the model's raw text back.
    fn complete(&self, prompt: &str) -> Result<String>;
    /// Same, but the answer must be a JSON object. Models without a JSON mode
    /// fall back to `complete`; the caller still validates the answer.
    fn complete_json(&self, prompt: &str) -> Result<String> {
        self.complete(prompt)
    }
    /// Short name for reports, e.g. "ollama:qwen2.5-coder:7b".
    fn name(&self) -> String;
}

/// Tier 1: a local open-weights model served by Ollama.
pub struct Ollama {
    url: String,
    model: String,
    num_ctx: u32,
    agent: ureq::Agent,
}

impl Ollama {
    pub fn new(url: &str, model: &str, num_ctx: u32, timeout: Duration) -> Self {
        let agent: ureq::Agent = ureq::Agent::config_builder()
            .timeout_global(Some(timeout))
            .build()
            .into();
        Self {
            url: url.trim_end_matches('/').to_string(),
            model: model.to_string(),
            num_ctx,
            agent,
        }
    }

    fn body(&self, prompt: &str) -> Value {
        self.body_with(prompt, false)
    }

    fn body_with(&self, prompt: &str, json_mode: bool) -> Value {
        let mut body = json!({
            "model": self.model,
            "prompt": prompt,
            "stream": false,
            "options": {
                // Low temperature: the same contract should give the same test.
                "temperature": 0.1,
                // Ollama silently drops the START of a prompt longer than its
                // context window, and the start is where our instructions are.
                "num_ctx": self.num_ctx
            }
        });
        if json_mode {
            // Ollama constrains the output to valid JSON.
            body["format"] = json!("json");
        }
        body
    }

    fn send(&self, body: Value) -> Result<String> {
        let endpoint = format!("{}/api/generate", self.url);
        let mut resp = self
            .agent
            .post(&endpoint)
            .send_json(body)
            .with_context(|| {
                format!(
                    "calling Ollama at {endpoint} \
                 (not running: start Ollama; HTTP 404: run `ollama pull {}`)",
                    self.model
                )
            })?;
        let v: Value = resp
            .body_mut()
            .read_json()
            .context("reading Ollama response")?;
        v.get("response")
            .and_then(Value::as_str)
            .map(str::to_string)
            .context("Ollama response has no `response` field")
    }
}

impl Model for Ollama {
    fn complete(&self, prompt: &str) -> Result<String> {
        self.send(self.body(prompt))
    }

    fn complete_json(&self, prompt: &str) -> Result<String> {
        self.send(self.body_with(prompt, true))
    }

    fn name(&self) -> String {
        format!("ollama:{}", self.model)
    }
}

/// Test double: returns canned answers in order and records every prompt.
#[cfg(test)]
pub struct Scripted {
    pub answers: std::cell::RefCell<std::collections::VecDeque<String>>,
    pub prompts: std::cell::RefCell<Vec<String>>,
}

#[cfg(test)]
impl Scripted {
    pub fn new(answers: &[&str]) -> Self {
        Self {
            answers: std::cell::RefCell::new(answers.iter().map(|s| s.to_string()).collect()),
            prompts: std::cell::RefCell::new(Vec::new()),
        }
    }
}

#[cfg(test)]
impl Model for Scripted {
    fn complete(&self, prompt: &str) -> Result<String> {
        self.prompts.borrow_mut().push(prompt.to_string());
        self.answers
            .borrow_mut()
            .pop_front()
            .context("scripted model ran out of answers")
    }
    fn name(&self) -> String {
        "scripted".into()
    }
}

#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn request_sets_context_window_and_disables_streaming() {
        let o = Ollama::new("http://host:11434/", "m", 8192, Duration::from_secs(1));
        let b = o.body("hi");
        assert_eq!(b["options"]["num_ctx"], 8192);
        assert_eq!(b["stream"], false);
        assert_eq!(o.url, "http://host:11434");
        assert!(b.get("format").is_none());
        assert_eq!(o.body_with("hi", true)["format"], "json");
    }
}
