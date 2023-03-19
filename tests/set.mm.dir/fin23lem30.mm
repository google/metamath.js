include "cfn.mm"
include "wcel.mm"
include "cv.mm"
include "ccom.mm"
include "cfv.mm"
include "crn.mm"
include "cint.mm"
include "cdif.mm"
include "cmpt.mm"
include "cif.mm"
include "wceq.mm"
include "wa.mm"
include "wn.mm"
include "wo.mm"
include "wfun.mm"
include "cuni.mm"
include "cin.mm"
include "c0.mm"
include "wi.mm"
include "eqif.mm"
include "biimpi.mm"
include "wral.mm"
include "cdm.mm"
include "wrex.mm"
include "wb.mm"
include "simpr.mm"
include "com.mm"
include "cen.mm"
include "wbr.mm"
include "crio.mm"
include "funmpt2.mm"
include "funco.mm"
include "sylancl.mm"
include "elunirn.mm"
include "syl.mm"
include "dmcoss.mm"
include "sseli.mm"
include "fvco.mm"
include "mpan.mm"
include "adantl.mm"
include "eleq2d.mm"
include "incom.mm"
include "wss.mm"
include "crab.mm"
include "wf1o.mm"
include "wf.mm"
include "difss.mm"
include "ominf.mm"
include "cun.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "undif.mm"
include "mpbi.mm"
include "unfi.mm"
include "syl5eqelr.mm"
include "ex.mm"
include "mtoi.mm"
include "ad2antrr.mm"
include "fin23lem22.mm"
include "sylancr.mm"
include "f1of.mm"
include "fdm.mm"
include "eleqtrd.mm"
include "ffvelrnd.mm"
include "eldifbd.mm"
include "eleq2i.mm"
include "sylnib.mm"
include "eldifad.mm"
include "fveq2.mm"
include "sseq2d.mm"
include "elrab3.mm"
include "mtbid.mm"
include "fin23lem20.mm"
include "orel1.mm"
include "sylc.mm"
include "syl5eq.mm"
include "disj.mm"
include "sylib.mm"
include "rsp.mm"
include "sylbid.mm"
include "syl5.mm"
include "rexlimdv.mm"
include "ralrimiv.mm"
include "sylibr.mm"
include "rneq.mm"
include "unieqd.mm"
include "ineq1d.mm"
include "eqeq1d.mm"
include "syl5ibr.mm"
include "expd.mm"
include "impcom.mm"
include "rncoss.mm"
include "unissi.mm"
include "cab.mm"
include "wex.mm"
include "eluniab.mm"
include "eleq2.mm"
include "eldifn.mm"
include "syl6bi.mm"
include "rexlimivw.mm"
include "exlimiv.mm"
include "sylbi.mm"
include "eqid.mm"
include "rnmpt.mm"
include "unieqi.mm"
include "eleq2s.mm"
include "mprgbir.mm"
include "ssdisj.mm"
include "mp2an.mm"
include "syl6eq.mm"
include "a1d.mm"
include "jaoi.mm"
include "mp2b.mm"

theorem fin23lem30
  let vx: setvar x
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let vt: setvar t
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cU: class U
  let vg: setvar g
  let vi: setvar i
  let cF: class F
  let cZ: class Z
  let va: setvar a
  let vc: setvar c
  let vb: setvar b
  let cA: class A
  let cB: class B
  let cV: class V
  let vf: setvar f
  let cG: class G
  assume fin23lem.a: |- U = seqom ( ( i e. _om , u e. _V |-> if ( ( ( t ` i ) i^i u ) = (/) , u , ( ( t ` i ) i^i u ) ) ) , U. ran t )
  assume fin23lem17.f: |- F = { g | A. a e. ( ~P g ^m _om ) ( A. x e. _om ( a ` suc x ) C_ ( a ` x ) -> |^| ran a e. ran a ) }
  assume fin23lem.b: |- P = { v e. _om | |^| ran U C_ ( t ` v ) }
  assume fin23lem.c: |- Q = ( w e. _om |-> ( iota_ x e. P ( x i^i P ) ~~ w ) )
  assume fin23lem.d: |- R = ( w e. _om |-> ( iota_ x e. ( _om \ P ) ( x i^i ( _om \ P ) ) ~~ w ) )
  assume fin23lem.e: |- Z = if ( P e. Fin , ( t o. R ) , ( ( z e. P |-> ( ( t ` z ) \ |^| ran U ) ) o. Q ) )

  disjoint g i
  disjoint g t
  disjoint g u
  disjoint g v
  disjoint g x
  disjoint g z
  disjoint i t
  disjoint i u
  disjoint i v
  disjoint i x
  disjoint i z
  disjoint t u
  disjoint t v
  disjoint t x
  disjoint t z
  disjoint u v
  disjoint u x
  disjoint u z
  disjoint v x
  disjoint v z
  disjoint x z
  disjoint a i
  disjoint a u
  disjoint a t
  disjoint F a
  disjoint F t
  disjoint a w
  disjoint a x
  disjoint a z
  disjoint P a
  disjoint w x
  disjoint w z
  disjoint P w
  disjoint P x
  disjoint P z
  disjoint a v
  disjoint R a
  disjoint R i
  disjoint R u
  disjoint R v
  disjoint U a
  disjoint U i
  disjoint U u
  disjoint U v
  disjoint U z
  disjoint Z a
  disjoint a g
  disjoint c g
  disjoint c i
  disjoint c t
  disjoint c u
  disjoint c v
  disjoint c x
  disjoint c z
  disjoint a b
  disjoint A a
  disjoint b i
  disjoint b u
  disjoint A b
  disjoint A i
  disjoint A u
  disjoint B a
  disjoint B b
  disjoint V a
  disjoint b w
  disjoint b x
  disjoint b z
  disjoint P b
  disjoint b v
  disjoint R b
  disjoint a c
  disjoint b c
  disjoint U b
  disjoint U c
  disjoint a f
  disjoint b f
  disjoint Z b
  disjoint Z f
  disjoint G a
  disjoint b g
  disjoint b t
  disjoint G b
  disjoint f g
  disjoint f t
  disjoint f x
  disjoint G f
  disjoint G g
  disjoint G t
  disjoint G x
  assert |- ( Fun t -> ( U. ran Z i^i |^| ran U ) = (/) )

  proof
    cZ
    cP
    cfn
    wcel
    #
    vt
    cv
    #
    cR
    ccom
    #
    vz
    cP
    vz
    cv
    @1
    cfv
    #
    cU
    crn
    cint
    #
    cdif
    #
    cmpt
    #
    cQ
    ccom
    #
    cif
    wceq
    #
    @0
    cZ
    @2
    wceq
    #
    wa
    #
    @0
    wn
    #
    cZ
    @7
    wceq
    #
    wa
    #
    wo
    #
    @1
    wfun
    #
    cZ
    crn
    #
    cuni
    #
    @4
    cin
    #
    c0
    wceq
    #
    wi
    #
    fin23lem.e
    @8
    @14
    @0
    cZ
    @2
    @7
    eqif
    biimpi
    @10
    @20
    @13
    @9
    @0
    @20
    @9
    @0
    @15
    @19
    @0
    @15
    wa
    #
    @19
    @9
    @2
    crn
    #
    cuni
    #
    @4
    cin
    #
    c0
    wceq
    #
    @21
    va
    cv
    #
    @4
    wcel
    wn
    #
    va
    @23
    wral
    @25
    @21
    @27
    va
    @23
    @21
    @26
    @23
    wcel
    #
    @26
    vb
    cv
    #
    @2
    cfv
    #
    wcel
    #
    vb
    @2
    cdm
    #
    wrex
    #
    @27
    @21
    @2
    wfun
    #
    @28
    @33
    wb
    @21
    @15
    cR
    wfun
    #
    @34
    @0
    @15
    simpr
    vw
    com
    vx
    cv
    com
    cP
    cdif
    #
    cin
    vw
    cv
    cen
    wbr
    vx
    @36
    crio
    cR
    fin23lem.d
    funmpt2
    #
    @1
    cR
    funco
    sylancl
    vb
    @26
    @2
    elunirn
    syl
    @21
    @31
    @27
    vb
    @32
    @29
    @32
    wcel
    @29
    cR
    cdm
    #
    wcel
    #
    @21
    @31
    @27
    wi
    #
    @32
    @38
    @29
    @1
    cR
    dmcoss
    sseli
    @21
    @39
    @40
    @21
    @39
    wa
    #
    @31
    @26
    @29
    cR
    cfv
    #
    @1
    cfv
    #
    wcel
    #
    @27
    @41
    @30
    @43
    @26
    @39
    @30
    @43
    wceq
    #
    @21
    @35
    @39
    @45
    @37
    @29
    @1
    cR
    fvco
    mpan
    adantl
    eleq2d
    @41
    @27
    va
    @43
    wral
    #
    @44
    @27
    wi
    @41
    @43
    @4
    cin
    #
    c0
    wceq
    @46
    @41
    @47
    @4
    @43
    cin
    #
    c0
    @43
    @4
    incom
    @41
    @4
    @43
    wss
    #
    wn
    @49
    @48
    c0
    wceq
    #
    wo
    #
    @50
    @41
    @42
    @4
    vv
    cv
    #
    @1
    cfv
    #
    wss
    #
    vv
    com
    crab
    #
    wcel
    #
    @49
    @41
    @42
    cP
    wcel
    @56
    @41
    @42
    com
    cP
    @41
    com
    @36
    @29
    cR
    @41
    com
    @36
    cR
    wf1o
    #
    com
    @36
    cR
    wf
    #
    @41
    @36
    com
    wss
    @36
    cfn
    wcel
    #
    wn
    #
    @57
    com
    cP
    difss
    @0
    @60
    @15
    @39
    @0
    @59
    com
    cfn
    wcel
    #
    ominf
    @0
    @59
    @61
    @0
    @59
    wa
    com
    cP
    @36
    cun
    #
    cfn
    cP
    com
    wss
    @62
    com
    wceq
    cP
    @55
    com
    fin23lem.b
    @54
    vv
    com
    ssrab2
    eqsstri
    cP
    com
    undif
    mpbi
    cP
    @36
    unfi
    syl5eqelr
    ex
    mtoi
    ad2antrr
    cR
    @36
    vw
    vx
    fin23lem.d
    fin23lem22
    sylancr
    com
    @36
    cR
    f1of
    syl
    #
    @41
    @29
    @38
    com
    @21
    @39
    simpr
    @41
    @58
    @38
    com
    wceq
    @63
    com
    @36
    cR
    fdm
    syl
    eleqtrd
    ffvelrnd
    #
    eldifbd
    cP
    @55
    @42
    fin23lem.b
    eleq2i
    sylnib
    @41
    @42
    com
    wcel
    #
    @56
    @49
    wb
    @41
    @42
    com
    cP
    @64
    eldifad
    #
    @54
    @49
    vv
    @42
    com
    @52
    @42
    wceq
    @53
    @43
    @4
    @52
    @42
    @1
    fveq2
    sseq2d
    elrab3
    syl
    mtbid
    @41
    @65
    @51
    @66
    vu
    vt
    @42
    cU
    vi
    fin23lem.a
    fin23lem20
    syl
    @49
    @50
    orel1
    sylc
    syl5eq
    va
    @43
    @4
    disj
    sylib
    @27
    va
    @43
    rsp
    syl
    sylbid
    ex
    syl5
    rexlimdv
    sylbid
    ralrimiv
    va
    @23
    @4
    disj
    sylibr
    @9
    @18
    @24
    c0
    @9
    @17
    @23
    @4
    @9
    @16
    @22
    cZ
    @2
    rneq
    unieqd
    ineq1d
    eqeq1d
    syl5ibr
    expd
    impcom
    @12
    @20
    @11
    @12
    @19
    @15
    @12
    @18
    @7
    crn
    #
    cuni
    #
    @4
    cin
    #
    c0
    @12
    @17
    @68
    @4
    @12
    @16
    @67
    cZ
    @7
    rneq
    unieqd
    ineq1d
    @68
    @6
    crn
    #
    cuni
    #
    wss
    @71
    @4
    cin
    c0
    wceq
    #
    @69
    c0
    wceq
    @67
    @70
    @6
    cQ
    rncoss
    unissi
    @72
    @27
    va
    @71
    va
    @71
    @4
    disj
    @27
    @26
    @29
    @5
    wceq
    #
    vz
    cP
    wrex
    #
    vb
    cab
    #
    cuni
    #
    @71
    @26
    @76
    wcel
    @26
    @29
    wcel
    #
    @74
    wa
    #
    vb
    wex
    @27
    @74
    vb
    @26
    eluniab
    @78
    @27
    vb
    @74
    @77
    @27
    @73
    @77
    @27
    wi
    vz
    cP
    @73
    @77
    @26
    @5
    wcel
    @27
    @29
    @5
    @26
    eleq2
    @26
    @3
    @4
    eldifn
    syl6bi
    rexlimivw
    impcom
    exlimiv
    sylbi
    @70
    @75
    vz
    vb
    cP
    @5
    @6
    @6
    eqid
    rnmpt
    unieqi
    eleq2s
    mprgbir
    @68
    @71
    @4
    ssdisj
    mp2an
    syl6eq
    a1d
    adantl
    jaoi
    mp2b
end
