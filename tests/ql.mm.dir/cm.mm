include "ax-r1.mm"

theorem cm
  let wva: term a
  let wvb: term b
  assume cm.1: |- a = b


  assert |- b = a

  proof
    wva
    wvb
    cm.1
    ax-r1
end
