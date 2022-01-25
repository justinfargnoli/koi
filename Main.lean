namespace Hidden

-- Defines a function that takes a name and produces a greeting.
def getGreeting (name : String) := s!"Hello, {name}! Isn't Lean great?"

end Hidden

def main : IO Unit :=
  -- Define a list of names
  let names := ["Sebastian", "Leo", "Daniel"]

  -- Map each name to a greeting
  let greetings := names.map Hidden.getGreeting

  -- Print the list of greetings
  for greeting in greetings do
    IO.println greeting