include "csh.mm"
include "wcel.mm"
include "chil.mm"
include "wss.mm"
include "cort.mm"
include "cfv.mm"
include "cv.mm"
include "csp.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "wb.mm"
include "shss.mm"
include "ocel.mm"
include "syl.mm"

theorem shocel
  let vx: setvar x
  let cA: class A
  let cH: class H
  let vy: setvar y
  let vz: setvar z
  let cB: class B

  disjoint H x
  disjoint A x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint H y
  disjoint H z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B y
  assert |- ( H e. SH -> ( A e. ( _|_ ` H ) <-> ( A e. ~H /\ A. x e. H ( A .ih x ) = 0 ) ) )

  proof
    cH
    csh
    wcel
    cH
    chil
    wss
    cA
    cH
    cort
    cfv
    wcel
    cA
    chil
    wcel
    cA
    vx
    cv
    csp
    co
    cc0
    wceq
    vx
    cH
    wral
    wa
    wb
    cH
    shss
    vx
    cA
    cH
    ocel
    syl
end
