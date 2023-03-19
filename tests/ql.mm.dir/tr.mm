include "ax-r2.mm"

theorem tr
  let wva: term a
  let wvb: term b
  let wvc: term c
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
