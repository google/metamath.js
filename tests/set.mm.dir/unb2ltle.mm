include "cxr.mm"
include "wss.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "wrex.mm"
include "cr.mm"
include "wral.mm"
include "cle.mm"
include "wa.mm"
include "nfv.mm"
include "nfra1.mm"
include "nfan.mm"
include "wcel.mm"
include "simpll.mm"
include "simpr.mm"
include "rspa.mm"
include "adantll.mm"
include "ssel2.mm"
include "ad4ant13.mm"
include "simpllr.mm"
include "rexrd.mm"
include "xrltled.mm"
include "ex.mm"
include "reximdva.mm"
include "imp.mm"
include "syl21anc.mm"
include "ralrimia.mm"
include "wceq.mm"
include "breq2.mm"
include "rexbidv.mm"
include "cbvralv.mm"
include "sylib.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "peano2rem.mm"
include "adantl.mm"
include "simpl.mm"
include "rspcva.mm"
include "syl2anc.mm"
include "syl.mm"
include "ltm1d.mm"
include "xrlelttrd.mm"
include "ralrimiva.mm"
include "impbid.mm"

theorem unb2ltle
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let cA: class A

  disjoint A w
  disjoint A x
  disjoint A y
  disjoint w x
  disjoint w y
  disjoint x y
  assert |- ( A C_ RR* -> ( A. w e. RR E. y e. A y < w <-> A. x e. RR E. y e. A y <_ x ) )

  proof
    cA
    cxr
    wss
    #
    vy
    cv
    #
    vw
    cv
    #
    clt
    wbr
    #
    vy
    cA
    wrex
    #
    vw
    cr
    wral
    #
    @1
    vx
    cv
    #
    cle
    wbr
    #
    vy
    cA
    wrex
    #
    vx
    cr
    wral
    #
    @0
    @5
    @9
    @0
    @5
    wa
    #
    @1
    @2
    cle
    wbr
    #
    vy
    cA
    wrex
    #
    vw
    cr
    wral
    @9
    @10
    @12
    vw
    cr
    @0
    @5
    vw
    @0
    vw
    nfv
    @4
    vw
    cr
    nfra1
    nfan
    @10
    @2
    cr
    wcel
    #
    wa
    @0
    @13
    @4
    @12
    @0
    @5
    @13
    simpll
    @10
    @13
    simpr
    @5
    @13
    @4
    @0
    @4
    vw
    cr
    rspa
    adantll
    @0
    @13
    wa
    #
    @4
    @12
    @14
    @3
    @11
    vy
    cA
    @14
    @1
    cA
    wcel
    #
    wa
    #
    @3
    @11
    @16
    @3
    wa
    #
    @1
    @2
    @0
    @15
    @1
    cxr
    wcel
    #
    @13
    @3
    cA
    cxr
    @1
    ssel2
    #
    ad4ant13
    @17
    @2
    @0
    @13
    @15
    @3
    simpllr
    rexrd
    @16
    @3
    simpr
    xrltled
    ex
    reximdva
    imp
    syl21anc
    ralrimia
    @12
    @8
    vw
    vx
    cr
    @2
    @6
    wceq
    @11
    @7
    vy
    cA
    @2
    @6
    @1
    cle
    breq2
    rexbidv
    cbvralv
    sylib
    ex
    @0
    @9
    @5
    @0
    @9
    wa
    #
    @4
    vw
    cr
    @20
    @13
    wa
    @0
    @13
    @1
    @2
    c1
    cmin
    co
    #
    cle
    wbr
    #
    vy
    cA
    wrex
    #
    @4
    @0
    @9
    @13
    simpll
    @20
    @13
    simpr
    @9
    @13
    @23
    @0
    @9
    @13
    wa
    @21
    cr
    wcel
    #
    @9
    @23
    @13
    @24
    @9
    @2
    peano2rem
    #
    adantl
    @9
    @13
    simpl
    @8
    @23
    vx
    @21
    cr
    @6
    @21
    wceq
    @7
    @22
    vy
    cA
    @6
    @21
    @1
    cle
    breq2
    rexbidv
    rspcva
    syl2anc
    adantll
    @14
    @23
    @4
    @14
    @22
    @3
    vy
    cA
    @16
    @22
    @3
    @16
    @22
    wa
    #
    @1
    @21
    @2
    @0
    @15
    @18
    @13
    @22
    @19
    ad4ant13
    @26
    @13
    @21
    cxr
    wcel
    @0
    @13
    @15
    @22
    simpllr
    #
    @13
    @21
    @25
    rexrd
    syl
    @26
    @2
    @27
    rexrd
    @16
    @22
    simpr
    @26
    @2
    @27
    ltm1d
    xrlelttrd
    ex
    reximdva
    imp
    syl21anc
    ralrimiva
    ex
    impbid
end
