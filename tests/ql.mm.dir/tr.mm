include "ax-r2.mm"

theorem tr
  param wva: term a
  param wvb: term b
  param wvc: term c
  assume tr.1: |- a = b
  assume tr.2: |- b = c


  assert |- a = c

  proof
    wva
    wvb
    wvc
    tr.1
    tr.2
    ax-r2
end
