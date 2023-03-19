
theorem idi
  param ta: term A
  param tr: term R
  assume idi.1: |- R |= A


  assert |- R |= A

  proof
    idi.1
end
