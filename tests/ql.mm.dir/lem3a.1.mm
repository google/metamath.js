include "wo.mm"
include "lem3.1.mm"
include "ax-r1.mm"
include "lor.mm"
include "oridm.mm"
include "ax-r2.mm"

theorem lem3a.1
  param wva: term a
  param wvb: term b
  assume lem3.1.1: |- ( a v b ) = b
  assume lem3.1.2: |- ( b ' v a ) = 1


  assert |- ( a v b ) = a

  proof
    wva
    wvb
    wo
    wva
    wva
    wo
    wva
    wvb
    wva
    wva
    wva
    wvb
    wva
    wvb
    lem3.1.1
    lem3.1.2
    lem3.1
    ax-r1
    lor
    wva
    oridm
    ax-r2
end
