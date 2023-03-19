include "word.mm"
include "wtr.mm"
include "cep.mm"
include "wwe.mm"
include "wa.mm"
include "wel.mm"
include "weq.mm"
include "w3o.mm"
include "wral.mm"
include "df-ord.mm"
include "cv.mm"
include "wbr.mm"
include "wfr.mm"
include "zfregfr.mm"
include "dfwe2.mm"
include "mpbiran.mm"
include "epel.mm"
include "biid.mm"
include "3orbi123i.mm"
include "2ralbii.mm"
include "bitri.mm"
include "anbi2i.mm"

theorem dford2
  let vx: setvar x
  let vy: setvar y
  let cA: class A

  disjoint x y
  disjoint A x
  disjoint A y
  assert |- ( Ord A <-> ( Tr A /\ A. x e. A A. y e. A ( x e. y \/ x = y \/ y e. x ) ) )

  proof
    cA
    word
    cA
    wtr
    #
    cA
    cep
    wwe
    #
    wa
    @0
    vx
    vy
    wel
    #
    vx
    vy
    weq
    #
    vy
    vx
    wel
    #
    w3o
    #
    vy
    cA
    wral
    vx
    cA
    wral
    #
    wa
    cA
    df-ord
    @1
    @6
    @0
    @1
    vx
    cv
    #
    vy
    cv
    #
    cep
    wbr
    #
    @3
    @8
    @7
    cep
    wbr
    #
    w3o
    #
    vy
    cA
    wral
    vx
    cA
    wral
    #
    @6
    @1
    cA
    cep
    wfr
    @12
    cA
    zfregfr
    vx
    vy
    cA
    cep
    dfwe2
    mpbiran
    @11
    @5
    vx
    vy
    cA
    cA
    @9
    @2
    @3
    @3
    @10
    @4
    vx
    vy
    epel
    @3
    biid
    vy
    vx
    epel
    3orbi123i
    2ralbii
    bitri
    anbi2i
    bitri
end
