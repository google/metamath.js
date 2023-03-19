include "copab.mm"
include "cres.mm"
include "cvv.mm"
include "cxp.mm"
include "cin.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "df-res.mm"
include "df-xp.mm"
include "vex.mm"
include "biantru.mm"
include "opabbii.mm"
include "eqtr4i.mm"
include "ineq2i.mm"
include "incom.mm"
include "eqtri.mm"
include "inopab.mm"

theorem resopab
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A

  disjoint x y
  disjoint A x
  disjoint A y
  assert |- ( { <. x , y >. | ph } |` A ) = { <. x , y >. | ( x e. A /\ ph ) }

  proof
    wph
    vx
    vy
    copab
    #
    cA
    cres
    @0
    cA
    cvv
    cxp
    #
    cin
    #
    vx
    cv
    cA
    wcel
    #
    wph
    wa
    vx
    vy
    copab
    #
    @0
    cA
    df-res
    @2
    @3
    vx
    vy
    copab
    #
    @0
    cin
    #
    @4
    @2
    @0
    @5
    cin
    @6
    @1
    @5
    @0
    @1
    @3
    vy
    cv
    cvv
    wcel
    #
    wa
    #
    vx
    vy
    copab
    @5
    vx
    vy
    cA
    cvv
    df-xp
    @3
    @8
    vx
    vy
    @7
    @3
    vy
    vex
    biantru
    opabbii
    eqtr4i
    ineq2i
    @0
    @5
    incom
    eqtri
    @3
    wph
    vx
    vy
    inopab
    eqtri
    eqtri
end
