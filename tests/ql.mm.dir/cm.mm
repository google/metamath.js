include "ax-r1.mm"

theorem cm
  param wva: term a
  param wvb: term b
  assume cm.1: |- a = b


  assert |- b = a

  proof
    wva
    wvb
    cm.1
    ax-r1
end
