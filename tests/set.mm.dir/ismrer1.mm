include "wcel.mm"
include "cr.mm"
include "csn.mm"
include "cmap.mm"
include "co.mm"
include "wf1o.mm"
include "cv.mm"
include "cfv.mm"
include "crrn.mm"
include "wceq.mm"
include "wral.mm"
include "cismty.mm"
include "cxp.mm"
include "cmpt.mm"
include "wb.mm"
include "sneq.mm"
include "xpeq1d.mm"
include "mpteq2dv.mm"
include "syl6eqr.mm"
include "f1oeq1.mm"
include "syl.mm"
include "oveq2d.mm"
include "f1oeq3.mm"
include "bitrd.mm"
include "eqid.mm"
include "reex.mm"
include "vex.mm"
include "mapsnf1o3.mm"
include "vtoclg.mm"
include "wa.mm"
include "cmin.mm"
include "c2.mm"
include "cexp.mm"
include "csu.mm"
include "csqrt.mm"
include "cabs.mm"
include "cc.mm"
include "xpeq2d.mm"
include "snex.mm"
include "xpex.mm"
include "fvmpt3i.mm"
include "fveq1d.mm"
include "adantr.mm"
include "cvv.mm"
include "snidg.mm"
include "fvconst2g.mm"
include "sylancr.mm"
include "sylan9eqr.mm"
include "adantl.mm"
include "oveq12d.mm"
include "oveq1d.mm"
include "resubcl.mm"
include "absresq.mm"
include "eqtr4d.mm"
include "recnd.mm"
include "abscld.mm"
include "sqcld.mm"
include "eqeltrd.mm"
include "fveq2.mm"
include "sumsn.mm"
include "syldan.mm"
include "eqtrd.mm"
include "fveq2d.mm"
include "absge0d.mm"
include "sqrtsqd.mm"
include "wf.mm"
include "f1of.mm"
include "ffvelrnda.mm"
include "anim12dan.mm"
include "cfn.mm"
include "snfi.mm"
include "rrnmval.mm"
include "mp3an1.mm"
include "remetdval.mm"
include "3eqtr4rd.mm"
include "ralrimivva.mm"
include "cxmt.mm"
include "rexmet.mm"
include "cme.mm"
include "rrnmet.mm"
include "metxmet.mm"
include "mp2b.mm"
include "isismty.mm"
include "mp2an.mm"
include "sylanbrc.mm"

theorem ismrer1
  let vx: setvar x
  let cA: class A
  let cR: class R
  let cF: class F
  let cV: class V
  let vk: setvar k
  let vy: setvar y
  let vz: setvar z
  assume ismrer1.1: |- R = ( ( abs o. - ) |` ( RR X. RR ) )
  assume ismrer1.2: |- F = ( x e. RR |-> ( { A } X. { x } ) )

  disjoint A x
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint A k
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint F k
  disjoint F y
  disjoint F z
  disjoint R y
  disjoint R z
  disjoint V k
  disjoint V y
  disjoint V z
  assert |- ( A e. V -> F e. ( R Ismty ( Rn ` { A } ) ) )

  proof
    cA
    cV
    wcel
    #
    cr
    cr
    cA
    csn
    #
    cmap
    co
    #
    cF
    wf1o
    #
    vy
    cv
    #
    vz
    cv
    #
    cR
    co
    #
    @4
    cF
    cfv
    #
    @5
    cF
    cfv
    #
    @1
    crrn
    cfv
    #
    co
    #
    wceq
    #
    vz
    cr
    wral
    vy
    cr
    wral
    #
    cF
    cR
    @9
    cismty
    co
    wcel
    #
    cr
    cr
    @4
    csn
    #
    cmap
    co
    #
    vx
    cr
    @14
    vx
    cv
    #
    csn
    #
    cxp
    #
    cmpt
    #
    wf1o
    #
    @3
    vy
    cA
    cV
    @4
    cA
    wceq
    #
    @20
    cr
    @15
    cF
    wf1o
    #
    @3
    @21
    @19
    cF
    wceq
    @20
    @22
    wb
    @21
    @19
    vx
    cr
    @1
    @17
    cxp
    #
    cmpt
    cF
    @21
    vx
    cr
    @18
    @23
    @21
    @14
    @1
    @17
    @4
    cA
    sneq
    #
    xpeq1d
    mpteq2dv
    ismrer1.2
    syl6eqr
    cr
    @15
    @19
    cF
    f1oeq1
    syl
    @21
    @15
    @2
    wceq
    @22
    @3
    wb
    @21
    @14
    @1
    cr
    cmap
    @24
    oveq2d
    @15
    @2
    cr
    cF
    f1oeq3
    syl
    bitrd
    vx
    cr
    @14
    @19
    @4
    @14
    eqid
    reex
    vy
    vex
    #
    @19
    eqid
    mapsnf1o3
    vtoclg
    #
    @0
    @11
    vy
    vz
    cr
    cr
    @0
    @4
    cr
    wcel
    #
    @5
    cr
    wcel
    #
    wa
    #
    wa
    #
    @1
    vk
    cv
    #
    @7
    cfv
    #
    @31
    @8
    cfv
    #
    cmin
    co
    #
    c2
    cexp
    co
    #
    vk
    csu
    #
    csqrt
    cfv
    #
    @4
    @5
    cmin
    co
    #
    cabs
    cfv
    #
    @10
    @6
    @30
    @37
    @39
    c2
    cexp
    co
    #
    csqrt
    cfv
    @39
    @30
    @36
    @40
    csqrt
    @30
    @36
    cA
    @7
    cfv
    #
    cA
    @8
    cfv
    #
    cmin
    co
    #
    c2
    cexp
    co
    #
    @40
    @0
    @29
    @44
    cc
    wcel
    @36
    @44
    wceq
    @30
    @44
    @40
    cc
    @30
    @44
    @38
    c2
    cexp
    co
    #
    @40
    @30
    @43
    @38
    c2
    cexp
    @30
    @41
    @4
    @42
    @5
    cmin
    @29
    @0
    @41
    cA
    @1
    @14
    cxp
    #
    cfv
    #
    @4
    @27
    @41
    @47
    wceq
    @28
    @27
    cA
    @7
    @46
    vx
    @4
    @23
    @46
    cr
    cF
    @16
    @4
    wceq
    @17
    @14
    @1
    @16
    @4
    sneq
    xpeq2d
    ismrer1.2
    @1
    @17
    cA
    snex
    @16
    snex
    xpex
    #
    fvmpt3i
    fveq1d
    adantr
    @0
    @4
    cvv
    wcel
    cA
    @1
    wcel
    #
    @47
    @4
    wceq
    @25
    cA
    cV
    snidg
    #
    @1
    @4
    cA
    cvv
    fvconst2g
    sylancr
    sylan9eqr
    @29
    @0
    @42
    cA
    @1
    @5
    csn
    #
    cxp
    #
    cfv
    #
    @5
    @28
    @42
    @53
    wceq
    @27
    @28
    cA
    @8
    @52
    vx
    @5
    @23
    @52
    cr
    cF
    @16
    @5
    wceq
    @17
    @51
    @1
    @16
    @5
    sneq
    xpeq2d
    ismrer1.2
    @48
    fvmpt3i
    fveq1d
    adantl
    @0
    @5
    cvv
    wcel
    @49
    @53
    @5
    wceq
    vz
    vex
    @50
    @1
    @5
    cA
    cvv
    fvconst2g
    sylancr
    sylan9eqr
    oveq12d
    oveq1d
    @30
    @38
    cr
    wcel
    #
    @40
    @45
    wceq
    @29
    @54
    @0
    @4
    @5
    resubcl
    adantl
    #
    @38
    absresq
    syl
    eqtr4d
    #
    @30
    @39
    @30
    @39
    @30
    @38
    @30
    @38
    @55
    recnd
    #
    abscld
    #
    recnd
    sqcld
    eqeltrd
    @35
    @44
    vk
    cA
    cV
    @31
    cA
    wceq
    #
    @34
    @43
    c2
    cexp
    @59
    @32
    @41
    @33
    @42
    cmin
    @31
    cA
    @7
    fveq2
    @31
    cA
    @8
    fveq2
    oveq12d
    oveq1d
    sumsn
    syldan
    @56
    eqtrd
    fveq2d
    @30
    @39
    @58
    @30
    @38
    @57
    absge0d
    sqrtsqd
    eqtrd
    @30
    @7
    @2
    wcel
    #
    @8
    @2
    wcel
    #
    wa
    @10
    @37
    wceq
    #
    @0
    @27
    @60
    @28
    @61
    @0
    cr
    @2
    @4
    cF
    @0
    @3
    cr
    @2
    cF
    wf
    @26
    cr
    @2
    cF
    f1of
    syl
    #
    ffvelrnda
    @0
    cr
    @2
    @5
    cF
    @63
    ffvelrnda
    anim12dan
    @1
    cfn
    wcel
    #
    @60
    @61
    @62
    cA
    snfi
    #
    vk
    @7
    @8
    @1
    @2
    @2
    eqid
    #
    rrnmval
    mp3an1
    syl
    @29
    @6
    @39
    wceq
    @0
    @4
    @5
    cR
    ismrer1.1
    remetdval
    adantl
    3eqtr4rd
    ralrimivva
    cR
    cr
    cxmt
    cfv
    wcel
    @9
    @2
    cxmt
    cfv
    wcel
    #
    @13
    @3
    @12
    wa
    wb
    cR
    ismrer1.1
    rexmet
    @64
    @9
    @2
    cme
    cfv
    wcel
    @67
    @65
    @1
    @2
    @66
    rrnmet
    @9
    @2
    metxmet
    mp2b
    vy
    vz
    cF
    cR
    @9
    cr
    @2
    isismty
    mp2an
    sylanbrc
end
