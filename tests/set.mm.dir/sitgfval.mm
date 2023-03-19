include "cv.mm"
include "crn.mm"
include "csn.mm"
include "cdif.mm"
include "ccnv.mm"
include "cima.mm"
include "cfv.mm"
include "co.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cfn.mm"
include "wcel.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "wral.mm"
include "wa.mm"
include "cdm.mm"
include "cmbfm.mm"
include "crab.mm"
include "csitg.mm"
include "cvv.mm"
include "sitgval.mm"
include "wceq.mm"
include "simpr.mm"
include "rneqd.mm"
include "difeq1d.mm"
include "cnveqd.mm"
include "imaeq1d.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "mpteq12dv.mm"
include "oveq2d.mm"
include "sibfmbl.mm"
include "sibfrn.mm"
include "sibfima.mm"
include "ralrimiva.mm"
include "jca32.mm"
include "rneq.mm"
include "eleq1d.mm"
include "cnveq.mm"
include "raleqbidv.mm"
include "anbi12d.mm"
include "elrab.mm"
include "sylibr.mm"
include "ovexd.mm"
include "fvmptd.mm"

theorem sitgfval
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
  let cA: class A
  let vf: setvar f
  let vg: setvar g
  let vm: setvar m
  let vw: setvar w
  assume sitgval.b: |- B = ( Base ` W )
  assume sitgval.j: |- J = ( TopOpen ` W )
  assume sitgval.s: |- S = ( sigaGen ` J )
  assume sitgval.0: |- .0. = ( 0g ` W )
  assume sitgval.x: |- .x. = ( .s ` W )
  assume sitgval.h: |- H = ( RRHom ` ( Scalar ` W ) )
  assume sitgval.1: |- ( ph -> W e. V )
  assume sitgval.2: |- ( ph -> M e. U. ran measures )
  assume sibfmbl.1: |- ( ph -> F e. dom ( W sitg M ) )

  disjoint F x
  disjoint ph x
  disjoint F x
  disjoint M x
  disjoint W x
  disjoint .0. x
  disjoint A x
  disjoint f g
  disjoint B f
  disjoint B g
  disjoint f x
  disjoint F f
  disjoint g x
  disjoint F g
  disjoint H f
  disjoint M f
  disjoint M g
  disjoint S f
  disjoint S g
  disjoint W f
  disjoint .x. f
  disjoint .0. f
  disjoint .0. g
  disjoint f ph
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
  assert |- ( ph -> ( ( W sitg M ) ` F ) = ( W gsum ( x e. ( ran F \ { .0. } ) |-> ( ( H ` ( M ` ( `' F " { x } ) ) ) .x. x ) ) ) )

  proof
    wph
    vf
    cF
    cW
    vx
    vf
    cv
    #
    crn
    #
    c.0
    csn
    #
    cdif
    #
    @0
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
    cH
    cfv
    #
    @5
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    cW
    vx
    cF
    crn
    #
    @2
    cdif
    #
    cF
    ccnv
    #
    @6
    cima
    #
    cM
    cfv
    #
    cH
    cfv
    #
    @5
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    vg
    cv
    #
    crn
    #
    cfn
    wcel
    #
    @20
    ccnv
    #
    @6
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
    @21
    @2
    cdif
    #
    wral
    #
    wa
    #
    vg
    cM
    cdm
    cS
    cmbfm
    co
    #
    crab
    #
    cW
    cM
    csitg
    co
    cvv
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
    wph
    @0
    cF
    wceq
    #
    wa
    #
    @11
    @19
    cW
    cgsu
    @34
    vx
    @3
    @10
    @13
    @18
    @34
    @1
    @12
    @2
    @34
    @0
    cF
    wph
    @33
    simpr
    #
    rneqd
    difeq1d
    @34
    @9
    @17
    @5
    c.x
    @34
    @8
    @16
    cH
    @34
    @7
    @15
    cM
    @34
    @4
    @14
    @6
    @34
    @0
    cF
    @35
    cnveqd
    imaeq1d
    fveq2d
    fveq2d
    oveq1d
    mpteq12dv
    oveq2d
    wph
    cF
    @31
    wcel
    #
    @12
    cfn
    wcel
    #
    @16
    @26
    wcel
    #
    vx
    @13
    wral
    #
    wa
    #
    wa
    cF
    @32
    wcel
    wph
    @36
    @37
    @39
    wph
    cB
    cS
    c.x
    cF
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
    sibfmbl.1
    sibfmbl
    wph
    cB
    cS
    c.x
    cF
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
    sibfmbl.1
    sibfrn
    wph
    @38
    vx
    @13
    wph
    @5
    cB
    cS
    c.x
    cF
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
    sibfmbl.1
    sibfima
    ralrimiva
    jca32
    @30
    @40
    vg
    cF
    @31
    @20
    cF
    wceq
    #
    @22
    @37
    @29
    @39
    @41
    @21
    @12
    cfn
    @20
    cF
    rneq
    #
    eleq1d
    @41
    @27
    @38
    vx
    @28
    @13
    @41
    @21
    @12
    @2
    @42
    difeq1d
    @41
    @25
    @16
    @26
    @41
    @24
    @15
    cM
    @41
    @23
    @14
    @6
    @20
    cF
    cnveq
    imaeq1d
    fveq2d
    eleq1d
    raleqbidv
    anbi12d
    elrab
    sylibr
    wph
    cW
    @19
    cgsu
    ovexd
    fvmptd
end
