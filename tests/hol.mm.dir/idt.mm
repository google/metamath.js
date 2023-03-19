
theorem idt
  let hal: type al
  let ta: term A
  assume idt.1: |- A : al


  assert |- A : al

  proof
    idt.1
end
