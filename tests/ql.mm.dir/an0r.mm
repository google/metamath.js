include "wf.mm"
include "wa.mm"
include "ancom.mm"
include "an0.mm"
include "ax-r2.mm"

theorem an0r
  let wva: term a


  assert |- ( 0 ^ a ) = 0

  proof
    wf
    wva
    wa
    wva
    wf
    wa
    wf
    wf
    wva
    ancom
    wva
    an0
    ax-r2
end
