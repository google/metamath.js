
theorem idi
  let ta: term A
  let tr: term R
  assume idi.1: |- R |= A


  assert |- R |= A

  proof
    idi.1
end
