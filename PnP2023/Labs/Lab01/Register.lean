/-!
# Registration

* fill in your name, github username, zulip handle, and url for your lab repo.
* check details with `#eval details?`
* the command `lake exe lab1` should now work and give details about your registration.
* commit and push your changes to your repo.
-/
def name?: Option String := none
def github?: Option String := none
def zulip?: Option String := none
def lab_repo?: Option String := none

def details? : Option String := do
  let name ← name?
  let github ← github?
  let zulip ← zulip?
  let lab_repo ← lab_repo?
  pure $ s!"Name: {name}; Github username:{github}; Zulip handle: {zulip}; Lab repo url: {lab_repo})"

#eval details?

