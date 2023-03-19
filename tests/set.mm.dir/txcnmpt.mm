include "ccn.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "ctx.mm"
include "cuni.mm"
include "cxp.mm"
include "wf.mm"
include "ccnv.mm"
include "cv.mm"
include "cima.mm"
include "cmpt2.mm"
include "crn.mm"
include "wral.mm"
include "cfv.mm"
include "cop.mm"
include "eqid.mm"
include "cnf.mm"
include "adantr.mm"
include "ffvelrnda.mm"
include "adantl.mm"
include "opelxpi.mm"
include "syl2anc.mm"
include "fmptd.mm"
include "cin.mm"
include "crab.mm"
include "mptpreima.mm"
include "wfn.mm"
include "wb.mm"
include "ffn.mm"
include "elpreima.mm"
include "3syl.mm"
include "ibar.mm"
include "bitr4d.mm"
include "ad2antrr.mm"
include "anbi12d.mm"
include "elin.mm"
include "opelxp.mm"
include "3bitr4g.mm"
include "rabbi2dva.mm"
include "wss.mm"
include "wceq.mm"
include "cdm.mm"
include "inss1.mm"
include "cnvimass.mm"
include "sstri.mm"
include "fdm.mm"
include "syl.mm"
include "syl5sseq.mm"
include "sseqin2.mm"
include "sylib.mm"
include "eqtr3d.mm"
include "syl5eq.mm"
include "ctop.mm"
include "cntop1.mm"
include "cnima.mm"
include "ad2ant2r.mm"
include "ad2ant2l.mm"
include "inopn.mm"
include "syl3anc.mm"
include "eqeltrd.mm"
include "ralrimivva.mm"
include "cvv.mm"
include "vex.mm"
include "xpex.mm"
include "rgen2w.mm"
include "imaeq2.mm"
include "eleq1d.mm"
include "ralrnmpt2.mm"
include "ax-mp.mm"
include "sylibr.mm"
include "ctopon.mm"
include "toptopon.mm"
include "ctg.mm"
include "cntop2.mm"
include "txval.mm"
include "syl2an.mm"
include "txtopon.mm"
include "tgcn.mm"
include "mpbir2and.mm"

theorem txcnmpt
  let vx: setvar x
  let cR: class R
  let cS: class S
  let cU: class U
  let cF: class F
  let cG: class G
  let cH: class H
  let cW: class W
  let vr: setvar r
  let vs: setvar s
  let vz: setvar z
  assume txcnmpt.1: |- W = U. U
  assume txcnmpt.2: |- H = ( x e. W |-> <. ( F ` x ) , ( G ` x ) >. )

  disjoint F x
  disjoint G x
  disjoint R x
  disjoint S x
  disjoint U x
  disjoint W x
  disjoint r s
  disjoint r x
  disjoint r z
  disjoint F r
  disjoint s x
  disjoint s z
  disjoint F s
  disjoint x z
  disjoint F z
  disjoint G r
  disjoint G s
  disjoint G z
  disjoint R r
  disjoint R s
  disjoint R z
  disjoint S r
  disjoint S s
  disjoint S z
  disjoint H r
  disjoint H s
  disjoint H z
  disjoint U r
  disjoint U s
  disjoint U z
  disjoint W z
  assert |- ( ( F e. ( U Cn R ) /\ G e. ( U Cn S ) ) -> H e. ( U Cn ( R tX S ) ) )

  proof
    cF
    cU
    cR
    ccn
    co
    wcel
    #
    cG
    cU
    cS
    ccn
    co
    wcel
    #
    wa
    #
    cH
    cU
    cR
    cS
    ctx
    co
    #
    ccn
    co
    wcel
    cW
    cR
    cuni
    #
    cS
    cuni
    #
    cxp
    #
    cH
    wf
    cH
    ccnv
    #
    vz
    cv
    #
    cima
    #
    cU
    wcel
    #
    vz
    vr
    vs
    cR
    cS
    vr
    cv
    #
    vs
    cv
    #
    cxp
    #
    cmpt2
    #
    crn
    #
    wral
    #
    @2
    vx
    cW
    vx
    cv
    #
    cF
    cfv
    #
    @17
    cG
    cfv
    #
    cop
    #
    @6
    cH
    @2
    @17
    cW
    wcel
    #
    wa
    @18
    @4
    wcel
    @19
    @5
    wcel
    @20
    @6
    wcel
    @2
    cW
    @4
    @17
    cF
    @0
    cW
    @4
    cF
    wf
    #
    @1
    cF
    cU
    cR
    cW
    @4
    txcnmpt.1
    @4
    eqid
    #
    cnf
    adantr
    #
    ffvelrnda
    @2
    cW
    @5
    @17
    cG
    @1
    cW
    @5
    cG
    wf
    #
    @0
    cG
    cU
    cS
    cW
    @5
    txcnmpt.1
    @5
    eqid
    #
    cnf
    adantl
    #
    ffvelrnda
    @18
    @19
    @4
    @5
    opelxpi
    syl2anc
    txcnmpt.2
    fmptd
    @2
    @7
    @13
    cima
    #
    cU
    wcel
    #
    vs
    cS
    wral
    vr
    cR
    wral
    #
    @16
    @2
    @29
    vr
    vs
    cR
    cS
    @2
    @11
    cR
    wcel
    #
    @12
    cS
    wcel
    #
    wa
    #
    wa
    #
    @28
    cF
    ccnv
    @11
    cima
    #
    cG
    ccnv
    @12
    cima
    #
    cin
    #
    cU
    @34
    @28
    @20
    @13
    wcel
    #
    vx
    cW
    crab
    #
    @37
    vx
    cW
    @20
    @13
    cH
    txcnmpt.2
    mptpreima
    @34
    cW
    @37
    cin
    #
    @39
    @37
    @34
    @38
    vx
    cW
    @37
    @34
    @21
    wa
    #
    @17
    @35
    wcel
    #
    @17
    @36
    wcel
    #
    wa
    @18
    @11
    wcel
    #
    @19
    @12
    wcel
    #
    wa
    @17
    @37
    wcel
    @38
    @41
    @42
    @44
    @43
    @45
    @41
    @42
    @21
    @44
    wa
    #
    @44
    @41
    @22
    cF
    cW
    wfn
    @42
    @46
    wb
    @34
    @22
    @21
    @2
    @22
    @33
    @24
    adantr
    #
    adantr
    cW
    @4
    cF
    ffn
    cW
    @17
    @11
    cF
    elpreima
    3syl
    @21
    @44
    @46
    wb
    @34
    @21
    @44
    ibar
    adantl
    bitr4d
    @41
    @43
    @21
    @45
    wa
    #
    @45
    @41
    @25
    cG
    cW
    wfn
    @43
    @48
    wb
    @2
    @25
    @33
    @21
    @27
    ad2antrr
    cW
    @5
    cG
    ffn
    cW
    @17
    @12
    cG
    elpreima
    3syl
    @21
    @45
    @48
    wb
    @34
    @21
    @45
    ibar
    adantl
    bitr4d
    anbi12d
    @17
    @35
    @36
    elin
    @18
    @19
    @11
    @12
    opelxp
    3bitr4g
    rabbi2dva
    @34
    @37
    cW
    wss
    @40
    @37
    wceq
    @34
    cF
    cdm
    #
    @37
    cW
    @37
    @35
    @49
    @35
    @36
    inss1
    cF
    @11
    cnvimass
    sstri
    @34
    @22
    @49
    cW
    wceq
    @47
    cW
    @4
    cF
    fdm
    syl
    syl5sseq
    @37
    cW
    sseqin2
    sylib
    eqtr3d
    syl5eq
    @34
    cU
    ctop
    wcel
    #
    @35
    cU
    wcel
    #
    @36
    cU
    wcel
    #
    @37
    cU
    wcel
    @2
    @50
    @33
    @1
    @50
    @0
    cG
    cU
    cS
    cntop1
    adantl
    #
    adantr
    @0
    @31
    @51
    @1
    @32
    @11
    cF
    cU
    cR
    cnima
    ad2ant2r
    @1
    @32
    @52
    @0
    @31
    @12
    cG
    cU
    cS
    cnima
    ad2ant2l
    @35
    @36
    cU
    inopn
    syl3anc
    eqeltrd
    ralrimivva
    @13
    cvv
    wcel
    #
    vs
    cS
    wral
    vr
    cR
    wral
    @16
    @30
    wb
    @54
    vr
    vs
    cR
    cS
    @11
    @12
    vr
    vex
    vs
    vex
    xpex
    rgen2w
    @10
    @29
    vr
    vs
    vz
    cR
    cS
    @13
    @14
    cvv
    @14
    eqid
    @8
    @13
    wceq
    @9
    @28
    cU
    @8
    @13
    @7
    imaeq2
    eleq1d
    ralrnmpt2
    ax-mp
    sylibr
    @2
    vz
    @15
    cH
    cU
    @3
    cW
    @6
    @2
    @50
    cU
    cW
    ctopon
    cfv
    wcel
    @53
    cU
    cW
    txcnmpt.1
    toptopon
    sylib
    @0
    cR
    ctop
    wcel
    #
    cS
    ctop
    wcel
    #
    @3
    @15
    ctg
    cfv
    wceq
    @1
    cF
    cU
    cR
    cntop2
    #
    cG
    cU
    cS
    cntop2
    #
    vr
    vs
    @15
    cR
    cS
    ctop
    ctop
    @15
    eqid
    txval
    syl2an
    @0
    cR
    @4
    ctopon
    cfv
    wcel
    #
    cS
    @5
    ctopon
    cfv
    wcel
    #
    @3
    @6
    ctopon
    cfv
    wcel
    @1
    @0
    @55
    @59
    @57
    cR
    @4
    @23
    toptopon
    sylib
    @1
    @56
    @60
    @58
    cS
    @5
    @26
    toptopon
    sylib
    cR
    cS
    @4
    @5
    txtopon
    syl2an
    tgcn
    mpbir2and
end
