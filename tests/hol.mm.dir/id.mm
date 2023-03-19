include "ax-id.mm"

theorem id
  param tr: term R
  assume ax-id.1: |- R : bool


  assert |- R |= R

  proof
    tr
    ax-id.1
    ax-id
end
