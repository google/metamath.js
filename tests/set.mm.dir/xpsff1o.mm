include "cxp.mm"
include "c2o.mm"
include "cv.mm"
include "c0.mm"
include "wceq.mm"
include "cif.mm"
include "cixp.mm"
include "wf1o.mm"
include "wf1.mm"
include "wfo.mm"
include "wf.mm"
include "cfv.mm"
include "wi.mm"
include "wral.mm"
include "csn.mm"
include "ccda.mm"
include "co.mm"
include "ccnv.mm"
include "wcel.mm"
include "wa.mm"
include "xpsfrnel2.mm"
include "biimpri.mm"
include "rgen2.mm"
include "fmpt2.mm"
include "mpbi.mm"
include "c1st.mm"
include "c2nd.mm"
include "cop.mm"
include "1st2nd2.mm"
include "fveq2d.mm"
include "df-ov.mm"
include "xp1st.mm"
include "xp2nd.mm"
include "xpsfval.mm"
include "syl2anc.mm"
include "syl5eqr.mm"
include "eqtrd.mm"
include "eqeqan12d.mm"
include "fveq1.mm"
include "cvv.mm"
include "fvex.mm"
include "xpsc0.mm"
include "ax-mp.mm"
include "3eqtr3g.mm"
include "c1o.mm"
include "xpsc1.mm"
include "opeq12d.mm"
include "syl5ibr.mm"
include "sylbid.mm"
include "dff13.mm"
include "mpbir2an.mm"
include "wrex.mm"
include "wfn.mm"
include "xpsfrnel.mm"
include "simp2bi.mm"
include "simp3bi.mm"
include "ixpfn.mm"
include "xpsfeq.mm"
include "syl.mm"
include "eqtr2d.mm"
include "rspceov.mm"
include "syl3anc.mm"
include "rgen.mm"
include "foov.mm"
include "df-f1o.mm"

theorem xpsff1o
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cF: class F
  let va: setvar a
  let vb: setvar b
  let vw: setvar w
  let vz: setvar z
  let cV: class V
  let cX: class X
  let cY: class Y
  let cW: class W
  assume xpsff1o.f: |- F = ( x e. A , y e. B |-> `' ( { x } +c { y } ) )

  disjoint k x
  disjoint k y
  disjoint A k
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B k
  disjoint B x
  disjoint B y
  disjoint a b
  disjoint a k
  disjoint a w
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint A a
  disjoint b k
  disjoint b w
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint A b
  disjoint k w
  disjoint k z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint x z
  disjoint y z
  disjoint A z
  disjoint F a
  disjoint F b
  disjoint F w
  disjoint F z
  disjoint V k
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  disjoint B a
  disjoint B b
  disjoint B w
  disjoint B z
  disjoint W k
  assert |- F : ( A X. B ) -1-1-onto-> X_ k e. 2o if ( k = (/) , A , B )

  proof
    cA
    cB
    cxp
    #
    vk
    c2o
    vk
    cv
    c0
    wceq
    cA
    cB
    cif
    #
    cixp
    #
    cF
    wf1o
    @0
    @2
    cF
    wf1
    #
    @0
    @2
    cF
    wfo
    #
    @3
    @0
    @2
    cF
    wf
    #
    vz
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
    @6
    @8
    wceq
    #
    wi
    #
    vw
    @0
    wral
    vz
    @0
    wral
    vx
    cv
    #
    csn
    vy
    cv
    #
    csn
    ccda
    co
    ccnv
    #
    @2
    wcel
    #
    vy
    cB
    wral
    vx
    cA
    wral
    @5
    @16
    vx
    vy
    cA
    cB
    @16
    @13
    cA
    wcel
    @14
    cB
    wcel
    wa
    cA
    cB
    vk
    @13
    @14
    xpsfrnel2
    biimpri
    rgen2
    vx
    vy
    cA
    cB
    @15
    @2
    cF
    xpsff1o.f
    fmpt2
    mpbi
    #
    @12
    vz
    vw
    @0
    @0
    @6
    @0
    wcel
    #
    @8
    @0
    wcel
    #
    wa
    #
    @10
    @6
    c1st
    cfv
    #
    csn
    @6
    c2nd
    cfv
    #
    csn
    ccda
    co
    ccnv
    #
    @8
    c1st
    cfv
    #
    csn
    @8
    c2nd
    cfv
    #
    csn
    ccda
    co
    ccnv
    #
    wceq
    #
    @11
    @18
    @19
    @7
    @23
    @9
    @26
    @18
    @7
    @21
    @22
    cop
    #
    cF
    cfv
    #
    @23
    @18
    @6
    @28
    cF
    @6
    cA
    cB
    1st2nd2
    #
    fveq2d
    @18
    @29
    @21
    @22
    cF
    co
    #
    @23
    @21
    @22
    cF
    df-ov
    @18
    @21
    cA
    wcel
    @22
    cB
    wcel
    @31
    @23
    wceq
    @6
    cA
    cB
    xp1st
    @6
    cA
    cB
    xp2nd
    vx
    vy
    cA
    cB
    cF
    @21
    @22
    xpsff1o.f
    xpsfval
    syl2anc
    syl5eqr
    eqtrd
    @19
    @9
    @24
    @25
    cop
    #
    cF
    cfv
    #
    @26
    @19
    @8
    @32
    cF
    @8
    cA
    cB
    1st2nd2
    #
    fveq2d
    @19
    @33
    @24
    @25
    cF
    co
    #
    @26
    @24
    @25
    cF
    df-ov
    @19
    @24
    cA
    wcel
    @25
    cB
    wcel
    @35
    @26
    wceq
    @8
    cA
    cB
    xp1st
    @8
    cA
    cB
    xp2nd
    vx
    vy
    cA
    cB
    cF
    @24
    @25
    xpsff1o.f
    xpsfval
    syl2anc
    syl5eqr
    eqtrd
    eqeqan12d
    @27
    @11
    @20
    @28
    @32
    wceq
    @27
    @21
    @24
    @22
    @25
    @27
    c0
    @23
    cfv
    #
    c0
    @26
    cfv
    #
    @21
    @24
    c0
    @23
    @26
    fveq1
    @21
    cvv
    wcel
    @36
    @21
    wceq
    @6
    c1st
    fvex
    @21
    @22
    cvv
    xpsc0
    ax-mp
    @24
    cvv
    wcel
    @37
    @24
    wceq
    @8
    c1st
    fvex
    @24
    @25
    cvv
    xpsc0
    ax-mp
    3eqtr3g
    @27
    c1o
    @23
    cfv
    #
    c1o
    @26
    cfv
    #
    @22
    @25
    c1o
    @23
    @26
    fveq1
    @22
    cvv
    wcel
    @38
    @22
    wceq
    @6
    c2nd
    fvex
    @21
    @22
    cvv
    xpsc1
    ax-mp
    @25
    cvv
    wcel
    @39
    @25
    wceq
    @8
    c2nd
    fvex
    @24
    @25
    cvv
    xpsc1
    ax-mp
    3eqtr3g
    opeq12d
    @18
    @19
    @6
    @28
    @8
    @32
    @30
    @34
    eqeqan12d
    syl5ibr
    sylbid
    rgen2
    vz
    vw
    @0
    @2
    cF
    dff13
    mpbir2an
    @4
    @5
    @6
    va
    cv
    vb
    cv
    cF
    co
    wceq
    vb
    cB
    wrex
    va
    cA
    wrex
    #
    vz
    @2
    wral
    @17
    @40
    vz
    @2
    @6
    @2
    wcel
    #
    c0
    @6
    cfv
    #
    cA
    wcel
    #
    c1o
    @6
    cfv
    #
    cB
    wcel
    #
    @6
    @42
    @44
    cF
    co
    #
    wceq
    @40
    @41
    @6
    c2o
    wfn
    #
    @43
    @45
    cA
    cB
    vk
    @6
    xpsfrnel
    #
    simp2bi
    #
    @41
    @47
    @43
    @45
    @48
    simp3bi
    #
    @41
    @46
    @42
    csn
    @44
    csn
    ccda
    co
    ccnv
    #
    @6
    @41
    @43
    @45
    @46
    @51
    wceq
    @49
    @50
    vx
    vy
    cA
    cB
    cF
    @42
    @44
    xpsff1o.f
    xpsfval
    syl2anc
    @41
    @47
    @51
    @6
    wceq
    vk
    c2o
    @1
    @6
    ixpfn
    @6
    xpsfeq
    syl
    eqtr2d
    va
    vb
    cA
    cB
    @42
    @44
    @6
    cF
    rspceov
    syl3anc
    rgen
    va
    vb
    vz
    cA
    cB
    @2
    cF
    foov
    mpbir2an
    @0
    @2
    cF
    df-f1o
    mpbir2an
end
