def getName (name: String) := s!"Hello, {name}!"


def main : IO Unit :=
  let names := ["ramon", "Maria"]

  let greetings := names.map getName

  for greeting in greetings do
    IO.println greeting
