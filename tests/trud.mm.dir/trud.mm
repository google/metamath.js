include "ax-trud.mm"

theorem trud
  let tr: term R
  assume ax-trud.1: |- R : bool


  assert |- R |= T.

  step 0) tr(): term R
  step 1) ax-trud.1(): |- R : bool
  step 2) ax-trud(0, 1): |- R |= T.
end
