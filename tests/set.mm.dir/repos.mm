include "cc0.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "cr.mm"
include "cpnf.mm"
include "cioo.mm"
include "co.mm"
include "breq2.mm"
include "ioopos.mm"
include "elrab2.mm"

theorem repos
  let cA: class A
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B


  assert |- ( A e. ( 0 (,) +oo ) <-> ( A e. RR /\ 0 < A ) )

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
    cc0
    cpnf
    cioo
    co
    @0
    cA
    cc0
    clt
    breq2
    vx
    ioopos
    elrab2
end
