include "weq.mm"
include "copab.mm"
include "cres.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cid.mm"
include "resopab.mm"
include "equcom.mm"
include "opabbii.mm"
include "dfid3.mm"
include "eqtr4i.mm"
include "reseq1i.mm"
include "eqtr3i.mm"

theorem opabresid
  let vx: setvar x
  let vy: setvar y
  let cA: class A

  disjoint A x
  disjoint A y
  disjoint x y
  assert |- { <. x , y >. | ( x e. A /\ y = x ) } = ( _I |` A )

  proof
    vy
    vx
    weq
    #
    vx
    vy
    copab
    #
    cA
    cres
    vx
    cv
    cA
    wcel
    @0
    wa
    vx
    vy
    copab
    cid
    cA
    cres
    @0
    vx
    vy
    cA
    resopab
    @1
    cid
    cA
    @1
    vx
    vy
    weq
    #
    vx
    vy
    copab
    cid
    @0
    @2
    vx
    vy
    vy
    vx
    equcom
    opabbii
    vx
    vy
    dfid3
    eqtr4i
    reseq1i
    eqtr3i
end
