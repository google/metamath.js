include "cmpt.mm"
include "cgsu.mm"
include "co.mm"
include "cdm.mm"
include "c1st.mm"
include "cres.mm"
include "ccnv.mm"
include "cv.mm"
include "csn.mm"
include "cima.mm"
include "cfv.mm"
include "cvv.mm"
include "c0g.mm"
include "eqid.mm"
include "cfn.mm"
include "wcel.mm"
include "dmexg.mm"
include "syl.mm"
include "wrel.mm"
include "1stdm.mm"
include "sylan.mm"
include "wfo.mm"
include "wfn.mm"
include "wceq.mm"
include "fo1st.mm"
include "fofn.mm"
include "dffn5.mm"
include "biimpi.mm"
include "mp2b.mm"
include "reseq1i.mm"
include "wss.mm"
include "ssv.mm"
include "resmpt.mm"
include "ax-mp.mm"
include "eqtri.mm"
include "gsummpt2co.mm"
include "wa.mm"
include "c2nd.mm"
include "ccom.mm"
include "cxp.mm"
include "ccmn.mm"
include "adantr.mm"
include "imaexg.mm"
include "cop.mm"
include "adantl.mm"
include "simp-4l.mm"
include "simplr.mm"
include "syl2anc.mm"
include "eqeltrrd.mm"
include "vex.mm"
include "elimasn.mm"
include "simpr.mm"
include "eqeq1d.mm"
include "eqidd.mm"
include "rspcedvd.mm"
include "r19.29a.mm"
include "fmptd.mm"
include "imafi2.mm"
include "fvex.mm"
include "a1i.mm"
include "fsuppmptdm.mm"
include "wf1o.mm"
include "2ndconst.mm"
include "wb.mm"
include "1stpreimas.mm"
include "reseq2d.mm"
include "f1oeq1.mm"
include "mpbird.mm"
include "gsumf1o.mm"
include "csb.mm"
include "eleqtrd.mm"
include "xp2nd.mm"
include "ralrimiva.mm"
include "fo2nd.mm"
include "fmptcos.mm"
include "nfv.mm"
include "wnfc.mm"
include "xp1st.mm"
include "elsn.mm"
include "sylib.mm"
include "eqcomd.mm"
include "eqopi.mm"
include "syl12anc.mm"
include "csbiedf.mm"
include "mpteq2dva.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "eqtr2d.mm"
include "mpteq2da.mm"

theorem gsummpt2d
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cW: class W
  assume gsummpt2d.c: |- F/_ z C
  assume gsummpt2d.0: |- F/ y ph
  assume gsummpt2d.b: |- B = ( Base ` W )
  assume gsummpt2d.1: |- ( x = <. y , z >. -> C = D )
  assume gsummpt2d.r: |- ( ph -> Rel A )
  assume gsummpt2d.2: |- ( ph -> A e. Fin )
  assume gsummpt2d.m: |- ( ph -> W e. CMnd )
  assume gsummpt2d.3: |- ( ( ph /\ x e. A ) -> C e. B )

  disjoint A x
  disjoint A y
  disjoint A z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint C y
  disjoint D x
  disjoint W x
  disjoint W y
  disjoint ph x
  disjoint ph z
  assert |- ( ph -> ( W gsum ( x e. A |-> C ) ) = ( W gsum ( y e. dom A |-> ( W gsum ( z e. ( A " { y } ) |-> D ) ) ) ) )

  proof
    wph
    cW
    vx
    cA
    cC
    cmpt
    cgsu
    co
    cW
    vy
    cA
    cdm
    #
    cW
    vx
    c1st
    cA
    cres
    #
    ccnv
    vy
    cv
    #
    csn
    #
    cima
    #
    cC
    cmpt
    #
    cgsu
    co
    #
    cmpt
    #
    cgsu
    co
    cW
    vy
    @0
    cW
    vz
    cA
    @3
    cima
    #
    cD
    cmpt
    #
    cgsu
    co
    #
    cmpt
    #
    cgsu
    co
    wph
    vx
    vy
    cA
    cB
    cC
    vx
    cv
    #
    c1st
    cfv
    #
    @0
    @1
    cvv
    cW
    cW
    c0g
    cfv
    #
    gsummpt2d.b
    @14
    eqid
    #
    gsummpt2d.m
    gsummpt2d.2
    wph
    cA
    cfn
    wcel
    #
    @0
    cvv
    wcel
    gsummpt2d.2
    cA
    cfn
    dmexg
    syl
    gsummpt2d.3
    wph
    cA
    wrel
    #
    @12
    cA
    wcel
    #
    @13
    @0
    wcel
    gsummpt2d.r
    @12
    cA
    1stdm
    sylan
    @1
    vx
    cvv
    @13
    cmpt
    #
    cA
    cres
    #
    vx
    cA
    @13
    cmpt
    #
    c1st
    @19
    cA
    cvv
    cvv
    c1st
    wfo
    c1st
    cvv
    wfn
    #
    c1st
    @19
    wceq
    #
    fo1st
    cvv
    cvv
    c1st
    fofn
    @22
    @23
    vx
    cvv
    c1st
    dffn5
    biimpi
    mp2b
    reseq1i
    cA
    cvv
    wss
    @20
    @21
    wceq
    cA
    ssv
    vx
    cvv
    cA
    @13
    resmpt
    ax-mp
    eqtri
    gsummpt2co
    wph
    @7
    @11
    cW
    cgsu
    wph
    vy
    @0
    @6
    @10
    gsummpt2d.0
    wph
    @2
    @0
    wcel
    #
    wa
    #
    @10
    cW
    @9
    c2nd
    @4
    cres
    #
    ccom
    #
    cgsu
    co
    @6
    @25
    @8
    cB
    @3
    @8
    cxp
    #
    @9
    cW
    @26
    cvv
    @14
    gsummpt2d.b
    @15
    wph
    cW
    ccmn
    wcel
    @24
    gsummpt2d.m
    adantr
    @25
    @16
    @8
    cvv
    wcel
    wph
    @16
    @24
    gsummpt2d.2
    adantr
    cA
    @3
    cfn
    imaexg
    syl
    @25
    vz
    @8
    cD
    cB
    @9
    @25
    vz
    cv
    #
    @8
    wcel
    #
    wa
    #
    @12
    @2
    @29
    cop
    #
    wceq
    #
    cD
    cB
    wcel
    vx
    cA
    @31
    @18
    wa
    #
    @33
    wa
    #
    cC
    cD
    cB
    @33
    cC
    cD
    wceq
    #
    @34
    gsummpt2d.1
    adantl
    @35
    wph
    @18
    cC
    cB
    wcel
    wph
    @24
    @30
    @18
    @33
    simp-4l
    @31
    @18
    @33
    simplr
    gsummpt2d.3
    syl2anc
    eqeltrrd
    @31
    @33
    @32
    @32
    wceq
    vx
    @32
    cA
    @30
    @32
    cA
    wcel
    #
    @25
    @30
    @37
    cA
    @2
    @29
    vy
    vex
    vz
    vex
    elimasn
    biimpi
    adantl
    @31
    @33
    wa
    @12
    @32
    @32
    @31
    @33
    simpr
    eqeq1d
    @31
    @32
    eqidd
    rspcedvd
    r19.29a
    #
    @9
    eqid
    #
    fmptd
    @25
    vz
    @8
    @9
    cB
    cvv
    cD
    @14
    @39
    wph
    @8
    cfn
    wcel
    #
    @24
    wph
    @16
    @40
    gsummpt2d.2
    cA
    @3
    imafi2
    syl
    adantr
    @38
    @14
    cvv
    wcel
    @25
    cW
    c0g
    fvex
    a1i
    fsuppmptdm
    @25
    @28
    @8
    @26
    wf1o
    #
    @28
    @8
    c2nd
    @28
    cres
    #
    wf1o
    #
    @24
    @43
    wph
    @2
    @8
    @0
    2ndconst
    adantl
    @25
    @26
    @42
    wceq
    @41
    @43
    wb
    @25
    @4
    @28
    c2nd
    wph
    @17
    @24
    @4
    @28
    wceq
    #
    gsummpt2d.r
    cA
    @0
    @2
    1stpreimas
    sylan
    #
    reseq2d
    @28
    @8
    @26
    @42
    f1oeq1
    syl
    mpbird
    gsumf1o
    @25
    @27
    @5
    cW
    cgsu
    @25
    @27
    vx
    @4
    vz
    @12
    c2nd
    cfv
    #
    cD
    csb
    #
    cmpt
    @5
    @25
    vx
    vz
    @4
    @8
    @46
    cD
    @26
    @9
    @25
    @46
    @8
    wcel
    #
    vx
    @4
    @25
    @12
    @4
    wcel
    #
    wa
    #
    @12
    @28
    wcel
    #
    @48
    @50
    @12
    @4
    @28
    @25
    @49
    simpr
    @25
    @44
    @49
    @45
    adantr
    eleqtrd
    #
    @12
    @3
    @8
    xp2nd
    syl
    #
    ralrimiva
    @26
    vx
    @4
    @46
    cmpt
    #
    wceq
    @25
    @26
    vx
    cvv
    @46
    cmpt
    #
    @4
    cres
    #
    @54
    c2nd
    @55
    @4
    cvv
    cvv
    c2nd
    wfo
    c2nd
    cvv
    wfn
    #
    c2nd
    @55
    wceq
    #
    fo2nd
    cvv
    cvv
    c2nd
    fofn
    @57
    @58
    vx
    cvv
    c2nd
    dffn5
    biimpi
    mp2b
    reseq1i
    @4
    cvv
    wss
    @56
    @54
    wceq
    @4
    ssv
    vx
    cvv
    @4
    @46
    resmpt
    ax-mp
    eqtri
    a1i
    @25
    @9
    eqidd
    fmptcos
    @25
    vx
    @4
    @47
    cC
    @50
    vz
    @46
    cD
    cC
    @8
    @50
    vz
    nfv
    vz
    cC
    wnfc
    @50
    gsummpt2d.c
    a1i
    @53
    @50
    @29
    @46
    wceq
    #
    wa
    #
    cC
    cD
    @60
    @33
    @36
    @60
    @51
    @13
    @2
    wceq
    #
    @46
    @29
    wceq
    @33
    @50
    @51
    @59
    @52
    adantr
    #
    @60
    @13
    @3
    wcel
    #
    @61
    @60
    @51
    @63
    @62
    @12
    @3
    @8
    xp1st
    syl
    @13
    @2
    @12
    c1st
    fvex
    elsn
    sylib
    @60
    @29
    @46
    @50
    @59
    simpr
    eqcomd
    @12
    @2
    @29
    @3
    @8
    eqopi
    syl12anc
    gsummpt2d.1
    syl
    eqcomd
    csbiedf
    mpteq2dva
    eqtrd
    oveq2d
    eqtr2d
    mpteq2da
    oveq2d
    eqtrd
end
