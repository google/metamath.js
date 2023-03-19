include "ctsu.mm"
include "co.mm"
include "cgsu.mm"
include "csn.mm"
include "ccl.mm"
include "cfv.mm"
include "cv.mm"
include "wcel.mm"
include "wss.mm"
include "cres.mm"
include "wi.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wral.mm"
include "wrex.mm"
include "wa.mm"
include "cuni.mm"
include "c0.mm"
include "wne.mm"
include "ctopon.mm"
include "wceq.mm"
include "ctps.mm"
include "istps.mm"
include "sylib.mm"
include "toponuni.mm"
include "syl.mm"
include "eleq2d.mm"
include "csupp.mm"
include "cun.mm"
include "elfpw.mm"
include "simplbi.mm"
include "adantl.mm"
include "cdm.mm"
include "suppssdm.mm"
include "wf.mm"
include "fdm.mm"
include "syl5sseq.mm"
include "ad2antrr.mm"
include "unssd.mm"
include "simprbi.mm"
include "cfsupp.mm"
include "wbr.mm"
include "fsuppimpd.mm"
include "unfi.mm"
include "syl2anc.mm"
include "sylanbrc.mm"
include "wb.mm"
include "ssun1.mm"
include "id.mm"
include "syl5sseqr.mm"
include "pm5.5.mm"
include "reseq2.mm"
include "oveq2d.mm"
include "eleq1d.mm"
include "bitrd.mm"
include "rspcv.mm"
include "ccmn.mm"
include "ssun2.mm"
include "a1i.mm"
include "gsumres.mm"
include "sylibd.mm"
include "rexlimdva.mm"
include "adantr.mm"
include "simprr.mm"
include "simplrr.mm"
include "eqeltrd.mm"
include "expr.mm"
include "ralrimiva.mm"
include "sseq1.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "impbid.mm"
include "disjsn.mm"
include "necon2abii.mm"
include "syl6bb.mm"
include "imbi2d.mm"
include "ralbidva.mm"
include "anbi12d.mm"
include "eqid.mm"
include "eltsms.mm"
include "ctop.mm"
include "topontop.mm"
include "gsumcl.mm"
include "snssd.mm"
include "sseqtrd.mm"
include "elcls2.mm"
include "3bitr4d.mm"
include "eqrdv.mm"

theorem tsmsgsum
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let cJ: class J
  let cV: class V
  let c.0: class .0.
  let vy: setvar y
  let vz: setvar z
  let vu: setvar u
  let vx: setvar x
  assume tsmsid.b: |- B = ( Base ` G )
  assume tsmsid.z: |- .0. = ( 0g ` G )
  assume tsmsid.1: |- ( ph -> G e. CMnd )
  assume tsmsid.2: |- ( ph -> G e. TopSp )
  assume tsmsid.a: |- ( ph -> A e. V )
  assume tsmsid.f: |- ( ph -> F : A --> B )
  assume tsmsid.w: |- ( ph -> F finSupp .0. )
  assume tsmsgsum.j: |- J = ( TopOpen ` G )


  assert |- ( ph -> ( G tsums F ) = ( ( cls ` J ) ` { ( G gsum F ) } ) )

  proof
    wph
    vx
    cG
    cF
    ctsu
    co
    #
    cG
    cF
    cgsu
    co
    #
    csn
    #
    cJ
    ccl
    cfv
    cfv
    #
    wph
    vx
    cv
    #
    cB
    wcel
    #
    @4
    vu
    cv
    #
    wcel
    #
    vy
    cv
    #
    vz
    cv
    #
    wss
    #
    cG
    cF
    @9
    cres
    #
    cgsu
    co
    #
    @6
    wcel
    #
    wi
    #
    vz
    cA
    cpw
    cfn
    cin
    #
    wral
    #
    vy
    @15
    wrex
    #
    wi
    #
    vu
    cJ
    wral
    #
    wa
    @4
    cJ
    cuni
    #
    wcel
    #
    @7
    @6
    @2
    cin
    #
    c0
    wne
    #
    wi
    #
    vu
    cJ
    wral
    #
    wa
    #
    @4
    @0
    wcel
    @4
    @3
    wcel
    #
    wph
    @5
    @21
    @19
    @25
    wph
    cB
    @20
    @4
    wph
    cJ
    cB
    ctopon
    cfv
    wcel
    #
    cB
    @20
    wceq
    wph
    cG
    ctps
    wcel
    @28
    tsmsid.2
    cB
    cJ
    cG
    tsmsid.b
    tsmsgsum.j
    istps
    sylib
    #
    cB
    cJ
    toponuni
    syl
    #
    eleq2d
    wph
    @18
    @24
    vu
    cJ
    wph
    @6
    cJ
    wcel
    #
    wa
    #
    @17
    @23
    @7
    @32
    @17
    @1
    @6
    wcel
    #
    @23
    @32
    @17
    @33
    @32
    @16
    @33
    vy
    @15
    @32
    @8
    @15
    wcel
    #
    wa
    #
    @16
    cG
    cF
    @8
    cF
    c.0
    csupp
    co
    #
    cun
    #
    cres
    #
    cgsu
    co
    #
    @6
    wcel
    #
    @33
    @35
    @37
    @15
    wcel
    #
    @16
    @40
    wi
    @35
    @37
    cA
    wss
    @37
    cfn
    wcel
    #
    @41
    @35
    @8
    @36
    cA
    @34
    @8
    cA
    wss
    #
    @32
    @34
    @43
    @8
    cfn
    wcel
    #
    @8
    cA
    elfpw
    #
    simplbi
    adantl
    wph
    @36
    cA
    wss
    #
    @31
    @34
    wph
    cF
    cdm
    #
    @36
    cA
    cF
    c.0
    suppssdm
    wph
    cA
    cB
    cF
    wf
    #
    @47
    cA
    wceq
    tsmsid.f
    cA
    cB
    cF
    fdm
    syl
    syl5sseq
    #
    ad2antrr
    unssd
    @35
    @44
    @36
    cfn
    wcel
    #
    @42
    @34
    @44
    @32
    @34
    @43
    @44
    @45
    simprbi
    adantl
    @35
    cF
    c.0
    wph
    cF
    c.0
    cfsupp
    wbr
    #
    @31
    @34
    tsmsid.w
    ad2antrr
    #
    fsuppimpd
    @8
    @36
    unfi
    syl2anc
    @37
    cA
    elfpw
    sylanbrc
    @14
    @40
    vz
    @37
    @15
    @9
    @37
    wceq
    #
    @14
    @13
    @40
    @53
    @10
    @14
    @13
    wb
    @53
    @37
    @8
    @9
    @8
    @36
    ssun1
    @53
    id
    syl5sseqr
    @10
    @13
    pm5.5
    syl
    @53
    @12
    @39
    @6
    @53
    @11
    @38
    cG
    cgsu
    @9
    @37
    cF
    reseq2
    oveq2d
    eleq1d
    bitrd
    rspcv
    syl
    @35
    @39
    @1
    @6
    @35
    cA
    cB
    cF
    cG
    cV
    @37
    c.0
    tsmsid.b
    tsmsid.z
    wph
    cG
    ccmn
    wcel
    #
    @31
    @34
    tsmsid.1
    ad2antrr
    wph
    cA
    cV
    wcel
    #
    @31
    @34
    tsmsid.a
    ad2antrr
    wph
    @48
    @31
    @34
    tsmsid.f
    ad2antrr
    @36
    @37
    wss
    @35
    @36
    @8
    ssun2
    a1i
    @52
    gsumres
    eleq1d
    sylibd
    rexlimdva
    wph
    @31
    @33
    @17
    wph
    @31
    @33
    wa
    #
    wa
    #
    @36
    @15
    wcel
    #
    @36
    @9
    wss
    #
    @13
    wi
    #
    vz
    @15
    wral
    #
    @17
    wph
    @58
    @56
    wph
    @46
    @50
    @58
    @49
    wph
    cF
    c.0
    tsmsid.w
    fsuppimpd
    @36
    cA
    elfpw
    sylanbrc
    adantr
    @57
    @60
    vz
    @15
    @57
    @9
    @15
    wcel
    #
    @59
    @13
    @57
    @62
    @59
    wa
    #
    wa
    #
    @12
    @1
    @6
    @64
    cA
    cB
    cF
    cG
    cV
    @9
    c.0
    tsmsid.b
    tsmsid.z
    wph
    @54
    @56
    @63
    tsmsid.1
    ad2antrr
    wph
    @55
    @56
    @63
    tsmsid.a
    ad2antrr
    wph
    @48
    @56
    @63
    tsmsid.f
    ad2antrr
    @57
    @62
    @59
    simprr
    wph
    @51
    @56
    @63
    tsmsid.w
    ad2antrr
    gsumres
    wph
    @31
    @33
    @63
    simplrr
    eqeltrd
    expr
    ralrimiva
    @16
    @61
    vy
    @36
    @15
    @8
    @36
    wceq
    #
    @14
    @60
    vz
    @15
    @65
    @10
    @59
    @13
    @8
    @36
    @9
    sseq1
    imbi1d
    ralbidv
    rspcev
    syl2anc
    expr
    impbid
    @33
    @22
    c0
    @6
    @1
    disjsn
    necon2abii
    syl6bb
    imbi2d
    ralbidva
    anbi12d
    wph
    vz
    vy
    vu
    cA
    cB
    @4
    @15
    cF
    cG
    cJ
    cV
    tsmsid.b
    tsmsgsum.j
    @15
    eqid
    tsmsid.1
    tsmsid.2
    tsmsid.a
    tsmsid.f
    eltsms
    wph
    cJ
    ctop
    wcel
    #
    @2
    @20
    wss
    @27
    @26
    wb
    wph
    @28
    @66
    @29
    cB
    cJ
    topontop
    syl
    wph
    @2
    cB
    @20
    wph
    @1
    cB
    wph
    cA
    cB
    cF
    cG
    cV
    c.0
    tsmsid.b
    tsmsid.z
    tsmsid.1
    tsmsid.a
    tsmsid.f
    tsmsid.w
    gsumcl
    snssd
    @30
    sseqtrd
    vu
    @4
    @2
    cJ
    @20
    @20
    eqid
    elcls2
    syl2anc
    3bitr4d
    eqrdv
end
