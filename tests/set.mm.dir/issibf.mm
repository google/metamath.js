include "csitg.mm"
include "co.mm"
include "cdm.mm"
include "wcel.mm"
include "cmbfm.mm"
include "crn.mm"
include "cfn.mm"
include "ccnv.mm"
include "cv.mm"
include "csn.mm"
include "cima.mm"
include "cfv.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "cdif.mm"
include "wral.mm"
include "wa.mm"
include "w3a.mm"
include "crab.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cvv.mm"
include "sitgval.mm"
include "dmeqd.mm"
include "eqid.mm"
include "dmmpt.mm"
include "syl6eq.mm"
include "eleq2d.mm"
include "wceq.mm"
include "rneq.mm"
include "difeq1d.mm"
include "cnveq.mm"
include "imaeq1d.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "mpteq12dv.mm"
include "oveq2d.mm"
include "eleq1d.mm"
include "elrab.mm"
include "syl6bb.mm"
include "ovex.mm"
include "biantru.mm"
include "syl6bbr.mm"
include "raleqbidv.mm"
include "anbi12d.mm"
include "3anass.mm"

theorem issibf
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let cS: class S
  let c.x: class .x.
  let cF: class F
  let cH: class H
  let cJ: class J
  let cM: class M
  let cV: class V
  let cW: class W
  let c.0: class .0.
  let vf: setvar f
  let vm: setvar m
  let vw: setvar w
  let vg: setvar g
  assume sitgval.b: |- B = ( Base ` W )
  assume sitgval.j: |- J = ( TopOpen ` W )
  assume sitgval.s: |- S = ( sigaGen ` J )
  assume sitgval.0: |- .0. = ( 0g ` W )
  assume sitgval.x: |- .x. = ( .s ` W )
  assume sitgval.h: |- H = ( RRHom ` ( Scalar ` W ) )
  assume sitgval.1: |- ( ph -> W e. V )
  assume sitgval.2: |- ( ph -> M e. U. ran measures )

  disjoint F x
  disjoint M x
  disjoint W x
  disjoint .0. x
  disjoint f m
  disjoint f w
  disjoint B f
  disjoint m w
  disjoint B m
  disjoint B w
  disjoint f g
  disjoint f x
  disjoint F f
  disjoint g x
  disjoint F g
  disjoint H f
  disjoint H m
  disjoint H w
  disjoint M f
  disjoint g m
  disjoint g w
  disjoint M g
  disjoint m x
  disjoint M m
  disjoint w x
  disjoint M w
  disjoint S f
  disjoint S g
  disjoint S m
  disjoint S w
  disjoint W f
  disjoint W g
  disjoint W m
  disjoint W w
  disjoint .0. f
  disjoint .0. g
  disjoint .0. m
  disjoint .0. w
  disjoint .x. f
  disjoint .x. m
  disjoint .x. w
  assert |- ( ph -> ( F e. dom ( W sitg M ) <-> ( F e. ( dom M MblFnM S ) /\ ran F e. Fin /\ A. x e. ( ran F \ { .0. } ) ( M ` ( `' F " { x } ) ) e. ( 0 [,) +oo ) ) ) )

  proof
    wph
    cF
    cW
    cM
    csitg
    co
    #
    cdm
    #
    wcel
    #
    cF
    cM
    cdm
    cS
    cmbfm
    co
    #
    wcel
    #
    cF
    crn
    #
    cfn
    wcel
    #
    cF
    ccnv
    #
    vx
    cv
    #
    csn
    #
    cima
    #
    cM
    cfv
    #
    cc0
    cpnf
    cico
    co
    #
    wcel
    #
    vx
    @5
    c.0
    csn
    #
    cdif
    #
    wral
    #
    wa
    #
    wa
    #
    @4
    @6
    @16
    w3a
    wph
    @2
    cF
    vg
    cv
    #
    crn
    #
    cfn
    wcel
    #
    @19
    ccnv
    #
    @9
    cima
    #
    cM
    cfv
    #
    @12
    wcel
    #
    vx
    @20
    @14
    cdif
    #
    wral
    #
    wa
    #
    vg
    @3
    crab
    #
    wcel
    #
    @18
    wph
    @2
    @30
    cW
    vx
    @15
    @11
    cH
    cfv
    #
    @8
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cvv
    wcel
    #
    wa
    #
    @30
    wph
    @2
    cF
    cW
    vx
    vf
    cv
    #
    crn
    #
    @14
    cdif
    #
    @37
    ccnv
    #
    @9
    cima
    #
    cM
    cfv
    #
    cH
    cfv
    #
    @8
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cvv
    wcel
    #
    vf
    @29
    crab
    #
    wcel
    @36
    wph
    @1
    @48
    cF
    wph
    @1
    vf
    @29
    @46
    cmpt
    #
    cdm
    @48
    wph
    @0
    @49
    wph
    vx
    cB
    cS
    c.x
    vf
    vg
    cH
    cJ
    cM
    cV
    cW
    c.0
    sitgval.b
    sitgval.j
    sitgval.s
    sitgval.0
    sitgval.x
    sitgval.h
    sitgval.1
    sitgval.2
    sitgval
    dmeqd
    vf
    @29
    @46
    @49
    @49
    eqid
    dmmpt
    syl6eq
    eleq2d
    @47
    @35
    vf
    cF
    @29
    @37
    cF
    wceq
    #
    @46
    @34
    cvv
    @50
    @45
    @33
    cW
    cgsu
    @50
    vx
    @39
    @44
    @15
    @32
    @50
    @38
    @5
    @14
    @37
    cF
    rneq
    difeq1d
    @50
    @43
    @31
    @8
    c.x
    @50
    @42
    @11
    cH
    @50
    @41
    @10
    cM
    @50
    @40
    @7
    @9
    @37
    cF
    cnveq
    imaeq1d
    fveq2d
    fveq2d
    oveq1d
    mpteq12dv
    oveq2d
    eleq1d
    elrab
    syl6bb
    @35
    @30
    cW
    @33
    cgsu
    ovex
    biantru
    syl6bbr
    @28
    @17
    vg
    cF
    @3
    @19
    cF
    wceq
    #
    @21
    @6
    @27
    @16
    @51
    @20
    @5
    cfn
    @19
    cF
    rneq
    #
    eleq1d
    @51
    @25
    @13
    vx
    @26
    @15
    @51
    @20
    @5
    @14
    @52
    difeq1d
    @51
    @24
    @11
    @12
    @51
    @23
    @10
    cM
    @51
    @22
    @7
    @9
    @19
    cF
    cnveq
    imaeq1d
    fveq2d
    eleq1d
    raleqbidv
    anbi12d
    elrab
    syl6bb
    @4
    @6
    @16
    3anass
    syl6bbr
end
