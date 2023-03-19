include "cplusg.mm"
include "cfv.mm"
include "cof.mm"
include "cmps.mm"
include "co.mm"
include "cbs.mm"
include "cxp.mm"
include "cres.mm"
include "cv.mm"
include "cmpt2.mm"
include "wcel.mm"
include "w3a.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "cfn.mm"
include "cn0.mm"
include "cmap.mm"
include "crab.mm"
include "cmpt.mm"
include "wa.mm"
include "wceq.mm"
include "simpl1.mm"
include "eqid.mm"
include "simp2.mm"
include "psrelbas.mm"
include "ffvelrnda.mm"
include "syl.mm"
include "eleqtrrd.mm"
include "simp3.mm"
include "oveqrspc2v.mm"
include "syl12anc.mm"
include "mpteq2dva.mm"
include "cvv.mm"
include "wf.mm"
include "wfn.mm"
include "ffn.mm"
include "ovex.mm"
include "rabex.mm"
include "a1i.mm"
include "inidm.mm"
include "eqidd.mm"
include "offval.mm"
include "3eqtr4d.mm"
include "mpt2eq3dva.mm"
include "eqtr3d.mm"
include "psrbaspropd.mm"
include "mpt2eq12.mm"
include "syl2anc.mm"
include "eqtrd.mm"
include "ofmres.mm"
include "3eqtr4g.mm"
include "psrplusg.mm"

theorem psrplusgpropd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cR: class R
  let cS: class S
  let cI: class I
  let va: setvar a
  let vb: setvar b
  let vd: setvar d
  let vc: setvar c
  assume psrplusgpropd.b1: |- ( ph -> B = ( Base ` R ) )
  assume psrplusgpropd.b2: |- ( ph -> B = ( Base ` S ) )
  assume psrplusgpropd.p: |- ( ( ph /\ ( x e. B /\ y e. B ) ) -> ( x ( +g ` R ) y ) = ( x ( +g ` S ) y ) )

  disjoint ph y
  disjoint ph x
  disjoint B x
  disjoint B y
  disjoint x y
  disjoint R y
  disjoint R x
  disjoint S y
  disjoint S x
  disjoint a ph
  disjoint b ph
  disjoint d ph
  disjoint a b
  disjoint a d
  disjoint a y
  disjoint b d
  disjoint b y
  disjoint d y
  disjoint I a
  disjoint I b
  disjoint I d
  disjoint I c
  disjoint R a
  disjoint R b
  disjoint R d
  disjoint S a
  disjoint S b
  disjoint S d
  disjoint a x
  disjoint c d
  disjoint d x
  assert |- ( ph -> ( +g ` ( I mPwSer R ) ) = ( +g ` ( I mPwSer S ) ) )

  proof
    wph
    cR
    cplusg
    cfv
    #
    cof
    #
    cI
    cR
    cmps
    co
    #
    cbs
    cfv
    #
    @3
    cxp
    cres
    #
    cS
    cplusg
    cfv
    #
    cof
    #
    cI
    cS
    cmps
    co
    #
    cbs
    cfv
    #
    @8
    cxp
    cres
    #
    @2
    cplusg
    cfv
    #
    @7
    cplusg
    cfv
    #
    wph
    va
    vb
    @3
    @3
    va
    cv
    #
    vb
    cv
    #
    @1
    co
    #
    cmpt2
    #
    va
    vb
    @8
    @8
    @12
    @13
    @6
    co
    #
    cmpt2
    #
    @4
    @9
    wph
    @15
    va
    vb
    @3
    @3
    @16
    cmpt2
    #
    @17
    wph
    va
    vb
    @3
    @3
    @14
    @16
    wph
    @12
    @3
    wcel
    #
    @13
    @3
    wcel
    #
    w3a
    #
    vd
    vc
    cv
    ccnv
    cn
    cima
    cfn
    wcel
    #
    vc
    cn0
    cI
    cmap
    co
    #
    crab
    #
    vd
    cv
    #
    @12
    cfv
    #
    @25
    @13
    cfv
    #
    @0
    co
    #
    cmpt
    vd
    @24
    @26
    @27
    @5
    co
    #
    cmpt
    @14
    @16
    @21
    vd
    @24
    @28
    @29
    @21
    @25
    @24
    wcel
    #
    wa
    #
    wph
    @26
    cB
    wcel
    @27
    cB
    wcel
    @28
    @29
    wceq
    wph
    @19
    @20
    @30
    simpl1
    #
    @31
    @26
    cR
    cbs
    cfv
    #
    cB
    @21
    @24
    @33
    @25
    @12
    @21
    @3
    @24
    cR
    @2
    vc
    cI
    @33
    @12
    @2
    eqid
    #
    @33
    eqid
    #
    @24
    eqid
    #
    @3
    eqid
    #
    wph
    @19
    @20
    simp2
    psrelbas
    #
    ffvelrnda
    @31
    wph
    cB
    @33
    wceq
    @32
    psrplusgpropd.b1
    syl
    #
    eleqtrrd
    @31
    @27
    @33
    cB
    @21
    @24
    @33
    @25
    @13
    @21
    @3
    @24
    cR
    @2
    vc
    cI
    @33
    @13
    @34
    @35
    @36
    @37
    wph
    @19
    @20
    simp3
    psrelbas
    #
    ffvelrnda
    @39
    eleqtrrd
    wph
    vx
    vy
    cB
    cB
    @0
    @5
    @26
    @27
    psrplusgpropd.p
    oveqrspc2v
    syl12anc
    mpteq2dva
    @21
    vd
    @24
    @24
    @26
    @27
    @0
    @24
    @12
    @13
    cvv
    cvv
    @21
    @24
    @33
    @12
    wf
    @12
    @24
    wfn
    @38
    @24
    @33
    @12
    ffn
    syl
    #
    @21
    @24
    @33
    @13
    wf
    @13
    @24
    wfn
    @40
    @24
    @33
    @13
    ffn
    syl
    #
    @24
    cvv
    wcel
    @21
    @22
    vc
    @23
    cn0
    cI
    cmap
    ovex
    rabex
    a1i
    #
    @43
    @24
    inidm
    #
    @31
    @26
    eqidd
    #
    @31
    @27
    eqidd
    #
    offval
    @21
    vd
    @24
    @24
    @26
    @27
    @5
    @24
    @12
    @13
    cvv
    cvv
    @41
    @42
    @43
    @43
    @44
    @45
    @46
    offval
    3eqtr4d
    mpt2eq3dva
    wph
    @3
    @8
    wceq
    #
    @47
    @18
    @17
    wceq
    wph
    cR
    cS
    cI
    wph
    cB
    @33
    cS
    cbs
    cfv
    psrplusgpropd.b1
    psrplusgpropd.b2
    eqtr3d
    psrbaspropd
    #
    @48
    va
    vb
    @3
    @3
    @8
    @8
    @16
    mpt2eq12
    syl2anc
    eqtrd
    @3
    @3
    @0
    va
    vb
    ofmres
    @8
    @8
    @5
    va
    vb
    ofmres
    3eqtr4g
    @3
    @0
    @10
    cR
    @2
    cI
    @34
    @37
    @0
    eqid
    @10
    eqid
    psrplusg
    @8
    @5
    @11
    cS
    @7
    cI
    @7
    eqid
    @8
    eqid
    @5
    eqid
    @11
    eqid
    psrplusg
    3eqtr4g
end
