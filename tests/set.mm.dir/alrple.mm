include "cr.mm"
include "wcel.mm"
include "cxr.mm"
include "cle.mm"
include "wbr.mm"
include "cv.mm"
include "caddc.mm"
include "co.mm"
include "crp.mm"
include "wral.mm"
include "wb.mm"
include "rexr.mm"
include "xralrple.mm"
include "sylan.mm"

theorem alrple
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vy: setvar y

  disjoint A x
  disjoint B x
  disjoint x y
  disjoint A y
  disjoint B y
  assert |- ( ( A e. RR /\ B e. RR ) -> ( A <_ B <-> A. x e. RR+ A <_ ( B + x ) ) )

  proof
    cA
    cr
    wcel
    cA
    cxr
    wcel
    cB
    cr
    wcel
    cA
    cB
    cle
    wbr
    cA
    cB
    vx
    cv
    caddc
    co
    cle
    wbr
    vx
    crp
    wral
    wb
    cA
    rexr
    vx
    cA
    cB
    xralrple
    sylan
end
