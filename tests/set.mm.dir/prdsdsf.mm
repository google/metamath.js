include "cxp.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "cds.mm"
include "crn.mm"
include "csn.mm"
include "cun.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cmpt2.mm"
include "wcel.mm"
include "wral.mm"
include "wa.mm"
include "cle.mm"
include "wbr.mm"
include "wss.mm"
include "csb.mm"
include "cres.mm"
include "cvv.mm"
include "wceq.mm"
include "simpr.mm"
include "elex.mm"
include "syl.mm"
include "ralrimiva.mm"
include "adantr.mm"
include "nfcsb1v.mm"
include "nfel1.mm"
include "csbeq1a.mm"
include "eleq1d.mm"
include "rspc.mm"
include "mpan9.mm"
include "eqid.mm"
include "fvmpts.mm"
include "syl2anc.mm"
include "fveq2d.mm"
include "oveqd.mm"
include "simprl.mm"
include "prdsbascl.mm"
include "nfel2.mm"
include "fveq2.mm"
include "eleq12d.mm"
include "simprr.mm"
include "ovresd.mm"
include "eqtr4d.mm"
include "cxmt.mm"
include "nfcv.mm"
include "nffv.mm"
include "nfxp.mm"
include "nfres.mm"
include "nfel.mm"
include "sqxpeqd.mm"
include "reseq12d.mm"
include "syl5eq.mm"
include "xmetcl.mm"
include "syl3anc.mm"
include "eqeltrd.mm"
include "fmptd.mm"
include "frn.mm"
include "0xr.mm"
include "a1i.mm"
include "snssd.mm"
include "unssd.mm"
include "supxrcl.mm"
include "ssun2.mm"
include "c0ex.mm"
include "snss.mm"
include "mpbir.mm"
include "supxrub.mm"
include "sylancl.mm"
include "elxrge0.mm"
include "sylanbrc.mm"
include "ralrimivva.mm"
include "fmpt2.mm"
include "sylib.mm"
include "mptexg.mm"
include "cdm.mm"
include "dmmptg.mm"
include "prdsds.mm"
include "feq1d.mm"
include "mpbird.mm"

theorem prdsdsf
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let cD: class D
  let cR: class R
  let cS: class S
  let cE: class E
  let cI: class I
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vy: setvar y
  let vz: setvar z
  assume prdsdsf.y: |- Y = ( S Xs_ ( x e. I |-> R ) )
  assume prdsdsf.b: |- B = ( Base ` Y )
  assume prdsdsf.v: |- V = ( Base ` R )
  assume prdsdsf.e: |- E = ( ( dist ` R ) |` ( V X. V ) )
  assume prdsdsf.d: |- D = ( dist ` Y )
  assume prdsdsf.s: |- ( ph -> S e. W )
  assume prdsdsf.i: |- ( ph -> I e. X )
  assume prdsdsf.r: |- ( ( ph /\ x e. I ) -> R e. Z )
  assume prdsdsf.m: |- ( ( ph /\ x e. I ) -> E e. ( *Met ` V ) )

  disjoint I x
  disjoint ph x
  disjoint f g
  disjoint f h
  disjoint f y
  disjoint B f
  disjoint g h
  disjoint g y
  disjoint B g
  disjoint h y
  disjoint B h
  disjoint B y
  disjoint f z
  disjoint D f
  disjoint g z
  disjoint D g
  disjoint h z
  disjoint D h
  disjoint y z
  disjoint D y
  disjoint D z
  disjoint E z
  disjoint f x
  disjoint I f
  disjoint g x
  disjoint I g
  disjoint x y
  disjoint x z
  disjoint I y
  disjoint I z
  disjoint V z
  disjoint f ph
  disjoint g ph
  disjoint h x
  disjoint h ph
  disjoint ph y
  disjoint R f
  disjoint R g
  disjoint R y
  disjoint R z
  disjoint S f
  disjoint S g
  disjoint S y
  disjoint Y f
  disjoint Y g
  disjoint Y y
  assert |- ( ph -> D : ( B X. B ) --> ( 0 [,] +oo ) )

  proof
    wph
    cB
    cB
    cxp
    #
    cc0
    cpnf
    cicc
    co
    #
    cD
    wf
    @0
    @1
    vf
    vg
    cB
    cB
    vy
    cI
    vy
    cv
    #
    vf
    cv
    #
    cfv
    #
    @2
    vg
    cv
    #
    cfv
    #
    @2
    vx
    cI
    cR
    cmpt
    #
    cfv
    #
    cds
    cfv
    #
    co
    #
    cmpt
    #
    crn
    #
    cc0
    csn
    #
    cun
    #
    cxr
    clt
    csup
    #
    cmpt2
    #
    wf
    #
    wph
    @15
    @1
    wcel
    #
    vg
    cB
    wral
    vf
    cB
    wral
    @17
    wph
    @18
    vf
    vg
    cB
    cB
    wph
    @3
    cB
    wcel
    #
    @5
    cB
    wcel
    #
    wa
    #
    wa
    #
    @15
    cxr
    wcel
    #
    cc0
    @15
    cle
    wbr
    #
    @18
    @22
    @14
    cxr
    wss
    #
    @23
    @22
    @12
    @13
    cxr
    @22
    cI
    cxr
    @11
    wf
    @12
    cxr
    wss
    @22
    vy
    cI
    @10
    cxr
    @11
    @22
    @2
    cI
    wcel
    #
    wa
    #
    @10
    @4
    @6
    vx
    @2
    cR
    csb
    #
    cds
    cfv
    #
    vx
    @2
    cV
    csb
    #
    @30
    cxp
    #
    cres
    #
    co
    #
    cxr
    @27
    @10
    @4
    @6
    @29
    co
    @33
    @27
    @9
    @29
    @4
    @6
    @27
    @8
    @28
    cds
    @27
    @26
    @28
    cvv
    wcel
    #
    @8
    @28
    wceq
    @22
    @26
    simpr
    @22
    cR
    cvv
    wcel
    #
    vx
    cI
    wral
    #
    @26
    @34
    wph
    @36
    @21
    wph
    @35
    vx
    cI
    wph
    vx
    cv
    #
    cI
    wcel
    wa
    cR
    cZ
    wcel
    #
    @35
    prdsdsf.r
    cR
    cZ
    elex
    syl
    ralrimiva
    adantr
    #
    @35
    @34
    vx
    @2
    cI
    vx
    @28
    cvv
    vx
    @2
    cR
    nfcsb1v
    #
    nfel1
    @37
    @2
    wceq
    #
    cR
    @28
    cvv
    vx
    @2
    cR
    csbeq1a
    #
    eleq1d
    rspc
    mpan9
    vx
    @2
    cR
    cI
    @7
    cvv
    @7
    eqid
    fvmpts
    syl2anc
    fveq2d
    oveqd
    @27
    @4
    @6
    @29
    @30
    @22
    @37
    @3
    cfv
    #
    cV
    wcel
    #
    vx
    cI
    wral
    @26
    @4
    @30
    wcel
    #
    @22
    vx
    cB
    cR
    cS
    @3
    cI
    cV
    cW
    cX
    cvv
    cY
    prdsdsf.y
    prdsdsf.b
    wph
    cS
    cW
    wcel
    @21
    prdsdsf.s
    adantr
    #
    wph
    cI
    cX
    wcel
    #
    @21
    prdsdsf.i
    adantr
    #
    @39
    prdsdsf.v
    wph
    @19
    @20
    simprl
    prdsbascl
    @44
    @45
    vx
    @2
    cI
    vx
    @4
    @30
    vx
    @2
    cV
    nfcsb1v
    #
    nfel2
    @41
    @43
    @4
    cV
    @30
    @37
    @2
    @3
    fveq2
    vx
    @2
    cV
    csbeq1a
    #
    eleq12d
    rspc
    mpan9
    #
    @22
    @37
    @5
    cfv
    #
    cV
    wcel
    #
    vx
    cI
    wral
    @26
    @6
    @30
    wcel
    #
    @22
    vx
    cB
    cR
    cS
    @5
    cI
    cV
    cW
    cX
    cvv
    cY
    prdsdsf.y
    prdsdsf.b
    @46
    @48
    @39
    prdsdsf.v
    wph
    @19
    @20
    simprr
    prdsbascl
    @53
    @54
    vx
    @2
    cI
    vx
    @6
    @30
    @49
    nfel2
    @41
    @52
    @6
    cV
    @30
    @37
    @2
    @5
    fveq2
    @50
    eleq12d
    rspc
    mpan9
    #
    ovresd
    eqtr4d
    @27
    @32
    @30
    cxmt
    cfv
    #
    wcel
    #
    @45
    @54
    @33
    cxr
    wcel
    @22
    cE
    cV
    cxmt
    cfv
    #
    wcel
    #
    vx
    cI
    wral
    #
    @26
    @57
    wph
    @60
    @21
    wph
    @59
    vx
    cI
    prdsdsf.m
    ralrimiva
    adantr
    @59
    @57
    vx
    @2
    cI
    vx
    @32
    @56
    vx
    @29
    @31
    vx
    @28
    cds
    vx
    cds
    nfcv
    @40
    nffv
    vx
    @30
    @30
    @49
    @49
    nfxp
    nfres
    vx
    @30
    cxmt
    vx
    cxmt
    nfcv
    @49
    nffv
    nfel
    @41
    cE
    @32
    @58
    @56
    @41
    cE
    cR
    cds
    cfv
    #
    cV
    cV
    cxp
    #
    cres
    @32
    prdsdsf.e
    @41
    @61
    @29
    @62
    @31
    @41
    cR
    @28
    cds
    @42
    fveq2d
    @41
    cV
    @30
    @50
    sqxpeqd
    reseq12d
    syl5eq
    @41
    cV
    @30
    cxmt
    @50
    fveq2d
    eleq12d
    rspc
    mpan9
    @51
    @55
    @4
    @6
    @32
    @30
    xmetcl
    syl3anc
    eqeltrd
    @11
    eqid
    fmptd
    cI
    cxr
    @11
    frn
    syl
    @22
    cc0
    cxr
    cc0
    cxr
    wcel
    @22
    0xr
    a1i
    snssd
    unssd
    #
    @14
    supxrcl
    syl
    @22
    @25
    cc0
    @14
    wcel
    #
    @24
    @63
    @64
    @13
    @14
    wss
    @13
    @12
    ssun2
    cc0
    @14
    c0ex
    snss
    mpbir
    @14
    cc0
    supxrub
    sylancl
    @15
    elxrge0
    sylanbrc
    ralrimivva
    vf
    vg
    cB
    cB
    @15
    @1
    @16
    @16
    eqid
    fmpt2
    sylib
    wph
    @0
    @1
    cD
    @16
    wph
    vy
    cB
    cD
    cY
    @7
    cS
    vf
    vg
    cI
    cW
    cvv
    prdsdsf.y
    prdsdsf.s
    wph
    @47
    @7
    cvv
    wcel
    prdsdsf.i
    vx
    cI
    cR
    cX
    mptexg
    syl
    prdsdsf.b
    wph
    @38
    vx
    cI
    wral
    @7
    cdm
    cI
    wceq
    wph
    @38
    vx
    cI
    prdsdsf.r
    ralrimiva
    vx
    cI
    cR
    cZ
    dmmptg
    syl
    prdsdsf.d
    prdsds
    feq1d
    mpbird
end
