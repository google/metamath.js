
theorem idt
  param hal: type al
  param ta: term A
  assume idt.1: |- A : al


  assert |- A : al

  proof
    idt.1
end
