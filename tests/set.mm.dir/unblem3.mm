include "com.mm"
include "wss.mm"
include "cv.mm"
include "wcel.mm"
include "wrex.mm"
include "wral.mm"
include "wa.mm"
include "cfv.mm"
include "csuc.mm"
include "cdif.mm"
include "cint.mm"
include "con0.mm"
include "unblem2.mm"
include "imp.mm"
include "wi.mm"
include "omsson.mm"
include "sstr.mm"
include "mpan2.mm"
include "ssel.mm"
include "anc2li.mm"
include "syl.mm"
include "ad2antrr.mm"
include "mpd.mm"
include "onmindif.mm"
include "wceq.mm"
include "unblem1.mm"
include "ex.mm"
include "syld.mm"
include "suceq.mm"
include "difeq2d.mm"
include "inteqd.mm"
include "frsucmpt2.mm"
include "sylcom.mm"
include "eleqtrrd.mm"

theorem unblem3
  let vx: setvar x
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let cA: class A
  let cF: class F
  let vu: setvar u
  let vy: setvar y
  assume unblem.2: |- F = ( rec ( ( x e. _V |-> |^| ( A \ suc x ) ) , |^| A ) |` _om )

  disjoint v w
  disjoint v x
  disjoint v z
  disjoint A v
  disjoint w x
  disjoint w z
  disjoint A w
  disjoint x z
  disjoint A x
  disjoint A z
  disjoint F v
  disjoint F w
  disjoint F z
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint A u
  disjoint v y
  disjoint w y
  disjoint x y
  disjoint y z
  disjoint A y
  disjoint F u
  disjoint F y
  assert |- ( ( A C_ _om /\ A. w e. _om E. v e. A w e. v ) -> ( z e. _om -> ( F ` z ) e. ( F ` suc z ) ) )

  proof
    cA
    com
    wss
    #
    vw
    cv
    vv
    cv
    wcel
    vv
    cA
    wrex
    vw
    com
    wral
    #
    wa
    #
    vz
    cv
    #
    com
    wcel
    #
    @3
    cF
    cfv
    #
    @3
    csuc
    cF
    cfv
    #
    wcel
    @2
    @4
    wa
    #
    @5
    cA
    @5
    csuc
    #
    cdif
    #
    cint
    #
    @6
    @7
    cA
    con0
    wss
    #
    @5
    con0
    wcel
    #
    wa
    #
    @5
    @10
    wcel
    @7
    @5
    cA
    wcel
    #
    @13
    @2
    @4
    @14
    vx
    vz
    vw
    vv
    cA
    cF
    unblem.2
    unblem2
    #
    imp
    @0
    @14
    @13
    wi
    #
    @1
    @4
    @0
    @11
    @16
    @0
    com
    con0
    wss
    @11
    omsson
    cA
    com
    con0
    sstr
    mpan2
    @11
    @14
    @12
    cA
    con0
    @5
    ssel
    anc2li
    syl
    ad2antrr
    mpd
    cA
    @5
    onmindif
    syl
    @2
    @4
    @6
    @10
    wceq
    #
    @2
    @4
    @10
    cA
    wcel
    #
    @17
    @2
    @4
    @14
    @18
    @15
    @2
    @14
    @18
    vw
    vv
    @5
    cA
    unblem1
    ex
    syld
    @4
    @18
    @17
    vx
    vy
    cA
    cint
    @3
    cA
    vx
    cv
    #
    csuc
    #
    cdif
    #
    cint
    @10
    cA
    vy
    cv
    #
    csuc
    #
    cdif
    #
    cint
    cF
    cA
    unblem.2
    @22
    @19
    wceq
    #
    @24
    @21
    @25
    @23
    @20
    cA
    @22
    @19
    suceq
    difeq2d
    inteqd
    @22
    @5
    wceq
    #
    @24
    @9
    @26
    @23
    @8
    cA
    @22
    @5
    suceq
    difeq2d
    inteqd
    frsucmpt2
    ex
    sylcom
    imp
    eleqtrrd
    ex
end
