include "wcel.mm"
include "cpw.mm"
include "clly.mm"
include "cv.mm"
include "csn.mm"
include "wral.mm"
include "wa.mm"
include "wss.mm"
include "crest.mm"
include "co.mm"
include "w3a.mm"
include "wrex.mm"
include "simplr.mm"
include "simpr.mm"
include "vex.mm"
include "snelpw.mm"
include "sylib.mm"
include "vsnid.mm"
include "a1i.mm"
include "llyi.mm"
include "syl3anc.mm"
include "simpr1.mm"
include "simpr2.mm"
include "snssd.mm"
include "eqssd.mm"
include "oveq2d.mm"
include "wceq.mm"
include "simplll.mm"
include "restdis.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "simpr3.mm"
include "eqeltrrd.mm"
include "ex.mm"
include "rexlimdvw.mm"
include "mpd.mm"
include "ralrimiva.mm"
include "ctop.mm"
include "cin.mm"
include "distop.mm"
include "adantr.mm"
include "wi.mm"
include "elpwi.mm"
include "adantl.mm"
include "ssralv.mm"
include "syl.mm"
include "simprl.mm"
include "sstrd.mm"
include "snex.mm"
include "elpw.mm"
include "sylibr.mm"
include "elind.mm"
include "snidg.mm"
include "ad2antrl.mm"
include "simpll.mm"
include "simprr.mm"
include "eqeltrd.mm"
include "eleq2.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl12anc.mm"
include "expr.mm"
include "ralimdva.mm"
include "syld.mm"
include "imp.mm"
include "an32s.mm"
include "islly.mm"
include "sylanbrc.mm"
include "impbida.mm"

theorem dislly
  let vx: setvar x
  let cA: class A
  let cV: class V
  let cX: class X
  let va: setvar a
  let vj: setvar j
  let vn: setvar n
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let vs: setvar s
  let cJ: class J

  disjoint A x
  disjoint V x
  disjoint X x
  disjoint a j
  disjoint a n
  disjoint a t
  disjoint a u
  disjoint a v
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint j n
  disjoint j t
  disjoint j u
  disjoint j v
  disjoint j w
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint n t
  disjoint n u
  disjoint n v
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint t z
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint s u
  disjoint s v
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint A s
  disjoint A u
  disjoint A v
  disjoint A w
  disjoint A y
  disjoint V y
  disjoint X u
  disjoint X y
  disjoint s z
  disjoint J s
  disjoint J u
  disjoint J v
  disjoint J w
  disjoint J x
  disjoint J y
  disjoint J z
  assert |- ( X e. V -> ( ~P X e. Locally A <-> A. x e. X ~P { x } e. A ) )

  proof
    cX
    cV
    wcel
    #
    cX
    cpw
    #
    cA
    clly
    wcel
    #
    vx
    cv
    #
    csn
    #
    cpw
    #
    cA
    wcel
    #
    vx
    cX
    wral
    #
    @0
    @2
    wa
    #
    @6
    vx
    cX
    @8
    @3
    cX
    wcel
    #
    wa
    #
    vy
    cv
    #
    @4
    wss
    #
    @3
    @11
    wcel
    #
    @1
    @11
    crest
    co
    #
    cA
    wcel
    #
    w3a
    #
    vy
    @1
    wrex
    #
    @6
    @10
    @2
    @4
    @1
    wcel
    #
    @3
    @4
    wcel
    #
    @17
    @0
    @2
    @9
    simplr
    @10
    @9
    @18
    @8
    @9
    simpr
    @3
    cX
    vx
    vex
    snelpw
    sylib
    @19
    @10
    vx
    vsnid
    a1i
    vy
    cA
    @3
    @4
    @1
    llyi
    syl3anc
    @10
    @16
    @6
    vy
    @1
    @10
    @16
    @6
    @10
    @16
    wa
    #
    @14
    @5
    cA
    @20
    @14
    @1
    @4
    crest
    co
    #
    @5
    @20
    @11
    @4
    @1
    crest
    @20
    @11
    @4
    @10
    @12
    @13
    @15
    simpr1
    @20
    @3
    @11
    @10
    @12
    @13
    @15
    simpr2
    snssd
    eqssd
    oveq2d
    @20
    @0
    @4
    cX
    wss
    #
    @21
    @5
    wceq
    #
    @0
    @2
    @9
    @16
    simplll
    @20
    @3
    cX
    @8
    @9
    @16
    simplr
    snssd
    cX
    @4
    cV
    restdis
    #
    syl2anc
    eqtrd
    @10
    @12
    @13
    @15
    simpr3
    eqeltrrd
    ex
    rexlimdvw
    mpd
    ralrimiva
    @0
    @7
    wa
    #
    @1
    ctop
    wcel
    #
    @3
    vu
    cv
    #
    wcel
    #
    @1
    @27
    crest
    co
    #
    cA
    wcel
    #
    wa
    #
    vu
    @1
    @11
    cpw
    #
    cin
    #
    wrex
    #
    vx
    @11
    wral
    #
    vy
    @1
    wral
    @2
    @0
    @26
    @7
    cX
    cV
    distop
    adantr
    @25
    @35
    vy
    @1
    @0
    @11
    @1
    wcel
    #
    @7
    @35
    @0
    @36
    wa
    #
    @7
    @35
    @37
    @7
    @6
    vx
    @11
    wral
    #
    @35
    @37
    @11
    cX
    wss
    #
    @7
    @38
    wi
    @36
    @39
    @0
    @11
    cX
    elpwi
    adantl
    #
    @6
    vx
    @11
    cX
    ssralv
    syl
    @37
    @6
    @34
    vx
    @11
    @37
    @13
    @6
    @34
    @37
    @13
    @6
    wa
    #
    wa
    #
    @4
    @33
    wcel
    @19
    @21
    cA
    wcel
    #
    @34
    @42
    @1
    @32
    @4
    @42
    @22
    @18
    @42
    @4
    @11
    cX
    @42
    @3
    @11
    @37
    @13
    @6
    simprl
    snssd
    #
    @37
    @39
    @41
    @40
    adantr
    sstrd
    #
    @4
    cX
    @3
    snex
    #
    elpw
    sylibr
    @42
    @4
    @11
    wss
    @4
    @32
    wcel
    @44
    @4
    @11
    @46
    elpw
    sylibr
    elind
    @13
    @19
    @37
    @6
    @3
    @11
    snidg
    ad2antrl
    @42
    @21
    @5
    cA
    @42
    @0
    @22
    @23
    @0
    @36
    @41
    simpll
    @45
    @24
    syl2anc
    @37
    @13
    @6
    simprr
    eqeltrd
    @31
    @19
    @43
    wa
    vu
    @4
    @33
    @27
    @4
    wceq
    #
    @28
    @19
    @30
    @43
    @27
    @4
    @3
    eleq2
    @47
    @29
    @21
    cA
    @27
    @4
    @1
    crest
    oveq2
    eleq1d
    anbi12d
    rspcev
    syl12anc
    expr
    ralimdva
    syld
    imp
    an32s
    ralrimiva
    vy
    vx
    vu
    cA
    @1
    islly
    sylanbrc
    impbida
end
