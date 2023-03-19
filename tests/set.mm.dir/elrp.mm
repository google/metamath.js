include "cc0.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "cr.mm"
include "crp.mm"
include "breq2.mm"
include "df-rp.mm"
include "elrab2.mm"

theorem elrp
  let cA: class A
  let vx: setvar x


  assert |- ( A e. RR+ <-> ( A e. RR /\ 0 < A ) )

  proof
    cc0
    vx
    cv
    #
    clt
    wbr
    cc0
    cA
    clt
    wbr
    vx
    cA
    cr
    crp
    @0
    cA
    cc0
    clt
    breq2
    vx
    df-rp
    elrab2
end
