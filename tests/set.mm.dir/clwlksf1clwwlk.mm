include "cfusgr.mm"
include "wcel.mm"
include "cprime.mm"
include "wa.mm"
include "cclwwlkn.mm"
include "co.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "wf1.mm"
include "clwlksfclwwlk.mm"
include "c2nd.mm"
include "cc0.mm"
include "c1st.mm"
include "chash.mm"
include "cop.mm"
include "csubstr.mm"
include "cvv.mm"
include "simprl.mm"
include "ovex.mm"
include "fveq2.mm"
include "syl5eq.mm"
include "fveq2d.mm"
include "opeq2d.mm"
include "oveq12d.mm"
include "fvmptg.mm"
include "sylancl.mm"
include "simpr.mm"
include "jctir.mm"
include "adantl.mm"
include "syl.mm"
include "eqeq12d.mm"
include "cfz.mm"
include "clwlksfclwwlk1hashn.mm"
include "eqcomd.mm"
include "ad2antlr.mm"
include "cn.mm"
include "prmnn.mm"
include "clwlksf1clwwlklem.mm"
include "syl3anc.mm"
include "imp.mm"
include "cuspgr.mm"
include "cwlks.mm"
include "wb.mm"
include "cusgr.mm"
include "fusgrusgr.mm"
include "usgruspgr.mm"
include "ad3antrrr.mm"
include "cclwlks.mm"
include "crab.mm"
include "elrabi.mm"
include "clwlkwlk.mm"
include "eleq2s.mm"
include "anim12i.mm"
include "adantr.mm"
include "uspgr2wlkeq.mm"
include "mpbir2and.mm"
include "ex.mm"
include "sylbid.mm"
include "ralrimivva.mm"
include "dff13.mm"
include "sylanbrc.mm"

theorem clwlksf1clwwlk
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cG: class G
  let cN: class N
  let vc: setvar c
  let vi: setvar i
  let cW: class W
  let vx: setvar x
  let vf: setvar f
  let vw: setvar w
  let vy: setvar y
  let cU: class U
  let vu: setvar u
  assume clwlksfclwwlk.1: |- A = ( 1st ` c )
  assume clwlksfclwwlk.2: |- B = ( 2nd ` c )
  assume clwlksfclwwlk.c: |- C = { c e. ( ClWalks ` G ) | ( # ` A ) = N }
  assume clwlksfclwwlk.f: |- F = ( c e. C |-> ( B substr <. 0 , ( # ` A ) >. ) )

  disjoint G c
  disjoint N c
  disjoint C c
  disjoint F c
  disjoint A i
  disjoint B i
  disjoint G i
  disjoint c i
  disjoint W c
  disjoint C i
  disjoint G x
  disjoint i x
  disjoint N i
  disjoint C f
  disjoint C w
  disjoint f w
  disjoint F f
  disjoint F w
  disjoint c f
  disjoint c w
  disjoint G f
  disjoint G w
  disjoint N f
  disjoint N w
  disjoint W i
  disjoint G y
  disjoint N y
  disjoint U c
  disjoint U y
  disjoint c y
  disjoint W y
  disjoint i u
  disjoint i w
  disjoint u w
  disjoint C u
  disjoint F u
  disjoint G u
  disjoint c u
  disjoint N u
  assert |- ( ( G e. FinUSGraph /\ N e. Prime ) -> F : C -1-1-> ( N ClWWalksN G ) )

  proof
    cG
    cfusgr
    wcel
    #
    cN
    cprime
    wcel
    #
    wa
    #
    cC
    cN
    cG
    cclwwlkn
    co
    #
    cF
    wf
    vu
    cv
    #
    cF
    cfv
    #
    vw
    cv
    #
    cF
    cfv
    #
    wceq
    #
    @4
    @6
    wceq
    #
    wi
    #
    vw
    cC
    wral
    vu
    cC
    wral
    cC
    @3
    cF
    wf1
    cA
    cB
    cC
    cF
    cG
    cN
    vc
    clwlksfclwwlk.1
    clwlksfclwwlk.2
    clwlksfclwwlk.c
    clwlksfclwwlk.f
    clwlksfclwwlk
    @2
    @10
    vu
    vw
    cC
    cC
    @2
    @4
    cC
    wcel
    #
    @6
    cC
    wcel
    #
    wa
    #
    wa
    #
    @8
    @4
    c2nd
    cfv
    #
    cc0
    @4
    c1st
    cfv
    #
    chash
    cfv
    #
    cop
    #
    csubstr
    co
    #
    @6
    c2nd
    cfv
    #
    cc0
    @6
    c1st
    cfv
    #
    chash
    cfv
    #
    cop
    #
    csubstr
    co
    #
    wceq
    #
    @9
    @14
    @5
    @19
    @7
    @24
    @14
    @11
    @19
    cvv
    wcel
    @5
    @19
    wceq
    @2
    @11
    @12
    simprl
    #
    @15
    @18
    csubstr
    ovex
    vc
    @4
    cB
    cc0
    cA
    chash
    cfv
    #
    cop
    #
    csubstr
    co
    #
    @19
    cC
    cvv
    cF
    vc
    cv
    #
    @4
    wceq
    #
    cB
    @15
    @28
    @18
    csubstr
    @31
    cB
    @30
    c2nd
    cfv
    #
    @15
    clwlksfclwwlk.2
    @30
    @4
    c2nd
    fveq2
    syl5eq
    @31
    @27
    @17
    cc0
    @31
    cA
    @16
    chash
    @31
    cA
    @30
    c1st
    cfv
    #
    @16
    clwlksfclwwlk.1
    @30
    @4
    c1st
    fveq2
    syl5eq
    fveq2d
    opeq2d
    oveq12d
    clwlksfclwwlk.f
    fvmptg
    sylancl
    @14
    @12
    @24
    cvv
    wcel
    #
    wa
    #
    @7
    @24
    wceq
    @13
    @35
    @2
    @13
    @12
    @34
    @11
    @12
    simpr
    #
    @20
    @23
    csubstr
    ovex
    jctir
    adantl
    vc
    @6
    @29
    @24
    cC
    cvv
    cF
    @30
    @6
    wceq
    #
    cB
    @20
    @28
    @23
    csubstr
    @37
    cB
    @32
    @20
    clwlksfclwwlk.2
    @30
    @6
    c2nd
    fveq2
    syl5eq
    @37
    @27
    @22
    cc0
    @37
    cA
    @21
    chash
    @37
    cA
    @33
    @21
    clwlksfclwwlk.1
    @30
    @6
    c1st
    fveq2
    syl5eq
    fveq2d
    opeq2d
    oveq12d
    clwlksfclwwlk.f
    fvmptg
    syl
    eqeq12d
    @14
    @25
    @9
    @14
    @25
    wa
    #
    @9
    cN
    @22
    wceq
    #
    vi
    cv
    #
    @15
    cfv
    @40
    @20
    cfv
    wceq
    vi
    cc0
    cN
    cfz
    co
    wral
    #
    @13
    @39
    @2
    @25
    @12
    @39
    @11
    @12
    @22
    cN
    cA
    cB
    cC
    cF
    cG
    cN
    @6
    vc
    clwlksfclwwlk.1
    clwlksfclwwlk.2
    clwlksfclwwlk.c
    clwlksfclwwlk.f
    clwlksfclwwlk1hashn
    eqcomd
    adantl
    ad2antlr
    @14
    @25
    @41
    @14
    cN
    cn
    wcel
    #
    @11
    @12
    @25
    @41
    wi
    @1
    @42
    @0
    @13
    cN
    prmnn
    ad2antlr
    @26
    @13
    @12
    @2
    @36
    adantl
    vi
    cA
    cB
    cC
    @4
    cF
    cG
    cN
    @6
    vc
    clwlksfclwwlk.1
    clwlksfclwwlk.2
    clwlksfclwwlk.c
    clwlksfclwwlk.f
    clwlksf1clwwlklem
    syl3anc
    imp
    @38
    cG
    cuspgr
    wcel
    #
    @4
    cG
    cwlks
    cfv
    #
    wcel
    #
    @6
    @44
    wcel
    #
    wa
    #
    cN
    @17
    wceq
    #
    @9
    @39
    @41
    wa
    wb
    @0
    @43
    @1
    @13
    @25
    @0
    cG
    cusgr
    wcel
    @43
    cG
    fusgrusgr
    cG
    usgruspgr
    syl
    ad3antrrr
    @13
    @47
    @2
    @25
    @11
    @45
    @12
    @46
    @45
    @4
    @27
    cN
    wceq
    #
    vc
    cG
    cclwlks
    cfv
    #
    crab
    #
    cC
    @4
    @51
    wcel
    @4
    @50
    wcel
    @45
    @49
    vc
    @4
    @50
    elrabi
    cG
    @4
    clwlkwlk
    syl
    clwlksfclwwlk.c
    eleq2s
    @46
    @6
    @51
    cC
    @6
    @51
    wcel
    @6
    @50
    wcel
    @46
    @49
    vc
    @6
    @50
    elrabi
    cG
    @6
    clwlkwlk
    syl
    clwlksfclwwlk.c
    eleq2s
    anim12i
    ad2antlr
    @13
    @48
    @2
    @25
    @11
    @48
    @12
    @11
    @17
    cN
    cA
    cB
    cC
    cF
    cG
    cN
    @4
    vc
    clwlksfclwwlk.1
    clwlksfclwwlk.2
    clwlksfclwwlk.c
    clwlksfclwwlk.f
    clwlksfclwwlk1hashn
    eqcomd
    adantr
    ad2antlr
    vi
    @4
    @6
    cG
    cN
    uspgr2wlkeq
    syl3anc
    mpbir2and
    ex
    sylbid
    ralrimivva
    vu
    vw
    cC
    @3
    cF
    dff13
    sylanbrc
end
