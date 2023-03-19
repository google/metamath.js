include "wcel.mm"
include "cfin7.mm"
include "ccrd.mm"
include "cdm.mm"
include "cfn.mm"
include "wi.mm"
include "cv.mm"
include "cen.mm"
include "wbr.mm"
include "con0.mm"
include "com.mm"
include "cdif.mm"
include "wrex.mm"
include "wn.mm"
include "isfin7.mm"
include "ibi.mm"
include "isnum2.mm"
include "wa.mm"
include "ensym.mm"
include "simprl.mm"
include "enfi.mm"
include "onfin.mm"
include "sylan9bbr.mm"
include "biimprd.mm"
include "con3d.mm"
include "impcom.mm"
include "eldifd.mm"
include "simprr.mm"
include "jca.mm"
include "sylanr2.mm"
include "ex.mm"
include "reximdv2.mm"
include "com12.mm"
include "sylbi.mm"
include "con1d.mm"
include "syl5com.mm"
include "eldifi.mm"
include "isnumi.mm"
include "syl2an.mm"
include "rexlimiva.mm"
include "con3i.mm"
include "syl5ibr.mm"
include "fin17.mm"
include "a1i.mm"
include "jad.mm"
include "impbid2.mm"

theorem isfin7-2
  let cA: class A
  let cV: class V
  let vx: setvar x


  assert |- ( A e. V -> ( A e. Fin7 <-> ( A e. dom card -> A e. Fin ) ) )

  proof
    cA
    cV
    wcel
    #
    cA
    cfin7
    wcel
    #
    cA
    ccrd
    cdm
    wcel
    #
    cA
    cfn
    wcel
    #
    wi
    @1
    cA
    vx
    cv
    #
    cen
    wbr
    #
    vx
    con0
    com
    cdif
    #
    wrex
    #
    wn
    #
    @2
    @3
    @1
    @8
    vx
    cA
    cfin7
    isfin7
    ibi
    @2
    @3
    @7
    @2
    @4
    cA
    cen
    wbr
    #
    vx
    con0
    wrex
    #
    @3
    wn
    #
    @7
    wi
    vx
    cA
    isnum2
    @11
    @10
    @7
    @11
    @9
    @5
    vx
    con0
    @6
    @11
    @4
    con0
    wcel
    #
    @9
    wa
    @4
    @6
    wcel
    #
    @5
    wa
    #
    @9
    @11
    @12
    @5
    @14
    @4
    cA
    ensym
    @11
    @12
    @5
    wa
    #
    wa
    #
    @13
    @5
    @16
    @4
    con0
    com
    @11
    @12
    @5
    simprl
    @15
    @11
    @4
    com
    wcel
    #
    wn
    @15
    @17
    @3
    @15
    @3
    @17
    @5
    @3
    @4
    cfn
    wcel
    @12
    @17
    cA
    @4
    enfi
    @4
    onfin
    sylan9bbr
    biimprd
    con3d
    impcom
    eldifd
    @11
    @12
    @5
    simprr
    jca
    sylanr2
    ex
    reximdv2
    com12
    sylbi
    con1d
    syl5com
    @0
    @2
    @3
    @1
    @2
    wn
    @1
    @0
    @8
    @7
    @2
    @5
    @2
    vx
    @6
    @13
    @12
    @9
    @2
    @5
    @4
    con0
    com
    eldifi
    cA
    @4
    ensym
    @4
    cA
    isnumi
    syl2an
    rexlimiva
    con3i
    vx
    cA
    cV
    isfin7
    syl5ibr
    @3
    @1
    wi
    @0
    cA
    fin17
    a1i
    jad
    impbid2
end
