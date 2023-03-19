include "cvv.mm"
include "wcel.mm"
include "cmeas.mm"
include "crn.mm"
include "cuni.mm"
include "csitg.mm"
include "co.mm"
include "cv.mm"
include "cfn.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "cfv.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "cdif.mm"
include "wral.mm"
include "wa.mm"
include "cdm.mm"
include "cmbfm.mm"
include "crab.mm"
include "cmpt.mm"
include "cgsu.mm"
include "wceq.mm"
include "elexd.mm"
include "c0g.mm"
include "ctopn.mm"
include "csigagen.mm"
include "csca.mm"
include "crrh.mm"
include "cvsca.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "fveq2i.mm"
include "eqtri.mm"
include "syl6eqr.mm"
include "oveq2d.mm"
include "sneqd.mm"
include "difeq2d.mm"
include "raleqdv.mm"
include "anbi2d.mm"
include "rabeqbidv.mm"
include "id.mm"
include "fveq1d.mm"
include "eqidd.mm"
include "oveq123d.mm"
include "mpteq12dv.mm"
include "oveq12d.mm"
include "dmeq.mm"
include "oveq1d.mm"
include "fveq1.mm"
include "eleq1d.mm"
include "ralbidv.mm"
include "simpl.mm"
include "mpteq2dva.mm"
include "df-sitg.mm"
include "ovex.mm"
include "mptrabex.mm"
include "ovmpt2.mm"
include "syl2anc.mm"

theorem sitgval
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let cS: class S
  let c.x: class .x.
  let vf: setvar f
  let vg: setvar g
  let cH: class H
  let cJ: class J
  let cM: class M
  let cV: class V
  let cW: class W
  let c.0: class .0.
  let vm: setvar m
  let vw: setvar w
  let cF: class F
  assume sitgval.b: |- B = ( Base ` W )
  assume sitgval.j: |- J = ( TopOpen ` W )
  assume sitgval.s: |- S = ( sigaGen ` J )
  assume sitgval.0: |- .0. = ( 0g ` W )
  assume sitgval.x: |- .x. = ( .s ` W )
  assume sitgval.h: |- H = ( RRHom ` ( Scalar ` W ) )
  assume sitgval.1: |- ( ph -> W e. V )
  assume sitgval.2: |- ( ph -> M e. U. ran measures )

  disjoint B f
  disjoint f g
  disjoint f x
  disjoint g x
  disjoint H f
  disjoint M f
  disjoint M g
  disjoint M x
  disjoint S f
  disjoint S g
  disjoint W f
  disjoint W g
  disjoint W x
  disjoint .0. f
  disjoint .0. g
  disjoint .0. x
  disjoint .x. f
  disjoint f m
  disjoint f w
  disjoint m w
  disjoint B m
  disjoint B w
  disjoint F f
  disjoint F g
  disjoint F x
  disjoint H m
  disjoint H w
  disjoint g m
  disjoint g w
  disjoint m x
  disjoint M m
  disjoint w x
  disjoint M w
  disjoint S m
  disjoint S w
  disjoint W m
  disjoint W w
  disjoint .0. m
  disjoint .0. w
  disjoint .x. m
  disjoint .x. w
  assert |- ( ph -> ( W sitg M ) = ( f e. { g e. ( dom M MblFnM S ) | ( ran g e. Fin /\ A. x e. ( ran g \ { .0. } ) ( M ` ( `' g " { x } ) ) e. ( 0 [,) +oo ) ) } |-> ( W gsum ( x e. ( ran f \ { .0. } ) |-> ( ( H ` ( M ` ( `' f " { x } ) ) ) .x. x ) ) ) ) )

  proof
    wph
    cW
    cvv
    wcel
    cM
    cmeas
    crn
    cuni
    #
    wcel
    cW
    cM
    csitg
    co
    vf
    vg
    cv
    #
    crn
    #
    cfn
    wcel
    #
    @1
    ccnv
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
    @2
    c.0
    csn
    #
    cdif
    #
    wral
    #
    wa
    #
    vg
    cM
    cdm
    #
    cS
    cmbfm
    co
    #
    crab
    #
    cW
    vx
    vf
    cv
    #
    crn
    #
    @10
    cdif
    #
    @17
    ccnv
    @5
    cima
    #
    cM
    cfv
    #
    cH
    cfv
    #
    @4
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cmpt
    #
    wceq
    wph
    cW
    cV
    sitgval.1
    elexd
    sitgval.2
    vw
    vm
    cW
    cM
    cvv
    @0
    vf
    @3
    @6
    vm
    cv
    #
    cfv
    #
    @8
    wcel
    #
    vx
    @2
    vw
    cv
    #
    c0g
    cfv
    #
    csn
    #
    cdif
    #
    wral
    #
    wa
    #
    vg
    @27
    cdm
    #
    @30
    ctopn
    cfv
    #
    csigagen
    cfv
    #
    cmbfm
    co
    #
    crab
    #
    @30
    vx
    @18
    @32
    cdif
    #
    @20
    @27
    cfv
    #
    @30
    csca
    cfv
    #
    crrh
    cfv
    #
    cfv
    #
    @4
    @30
    cvsca
    cfv
    #
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cmpt
    @26
    csitg
    vf
    @3
    @29
    vx
    @11
    wral
    #
    wa
    #
    vg
    @36
    cS
    cmbfm
    co
    #
    crab
    #
    cW
    vx
    @19
    @42
    cH
    cfv
    #
    @4
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cmpt
    @30
    cW
    wceq
    #
    vf
    @40
    @49
    @53
    @57
    @58
    @35
    @51
    vg
    @39
    @52
    @58
    @38
    cS
    @36
    cmbfm
    @58
    @38
    cW
    ctopn
    cfv
    #
    csigagen
    cfv
    #
    cS
    @58
    @37
    @59
    csigagen
    @30
    cW
    ctopn
    fveq2
    fveq2d
    cS
    cJ
    csigagen
    cfv
    @60
    sitgval.s
    cJ
    @59
    csigagen
    sitgval.j
    fveq2i
    eqtri
    syl6eqr
    oveq2d
    @58
    @34
    @50
    @3
    @58
    @29
    vx
    @33
    @11
    @58
    @32
    @10
    @2
    @58
    @31
    c.0
    @58
    @31
    cW
    c0g
    cfv
    c.0
    @30
    cW
    c0g
    fveq2
    sitgval.0
    syl6eqr
    sneqd
    #
    difeq2d
    raleqdv
    anbi2d
    rabeqbidv
    @58
    @30
    cW
    @48
    @56
    cgsu
    @58
    id
    @58
    vx
    @41
    @47
    @19
    @55
    @58
    @32
    @10
    @18
    @61
    difeq2d
    @58
    @45
    @54
    @4
    @4
    @46
    c.x
    @58
    @46
    cW
    cvsca
    cfv
    c.x
    @30
    cW
    cvsca
    fveq2
    sitgval.x
    syl6eqr
    @58
    @42
    @44
    cH
    @58
    @44
    cW
    csca
    cfv
    #
    crrh
    cfv
    cH
    @58
    @43
    @62
    crrh
    @30
    cW
    csca
    fveq2
    fveq2d
    sitgval.h
    syl6eqr
    fveq1d
    @58
    @4
    eqidd
    oveq123d
    mpteq12dv
    oveq12d
    mpteq12dv
    @27
    cM
    wceq
    #
    vf
    @53
    @57
    @16
    @25
    @63
    @51
    @13
    vg
    @52
    @15
    @63
    @36
    @14
    cS
    cmbfm
    @27
    cM
    dmeq
    oveq1d
    @63
    @50
    @12
    @3
    @63
    @29
    @9
    vx
    @11
    @63
    @28
    @7
    @8
    @6
    @27
    cM
    fveq1
    eleq1d
    ralbidv
    anbi2d
    rabeqbidv
    @63
    @56
    @24
    cW
    cgsu
    @63
    vx
    @19
    @55
    @23
    @63
    @4
    @19
    wcel
    #
    wa
    #
    @54
    @22
    @4
    c.x
    @65
    @42
    @21
    cH
    @65
    @20
    @27
    cM
    @63
    @64
    simpl
    fveq1d
    fveq2d
    oveq1d
    mpteq2dva
    oveq2d
    mpteq12dv
    vx
    vw
    vf
    vg
    vm
    df-sitg
    @13
    vf
    vg
    @15
    @25
    @14
    cS
    cmbfm
    ovex
    mptrabex
    ovmpt2
    syl2anc
end
