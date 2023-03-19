include "csitg.mm"
include "co.mm"
include "cdm.mm"
include "wfn.mm"
include "crn.mm"
include "wss.mm"
include "wf.mm"
include "wfun.mm"
include "cv.mm"
include "cfn.mm"
include "wcel.mm"
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
include "cmbfm.mm"
include "crab.mm"
include "cmpt.mm"
include "cgsu.mm"
include "funmpt.mm"
include "sitgval.mm"
include "funeqd.mm"
include "mpbiri.mm"
include "funfn.mm"
include "sylib.mm"
include "ralrimiva.mm"
include "fnfvrnss.mm"
include "syl2anc.mm"
include "df-f.mm"
include "sylanbrc.mm"

theorem sitgf
  let wph: wff ph
  let cB: class B
  let cS: class S
  let c.x: class .x.
  let vf: setvar f
  let cH: class H
  let cJ: class J
  let cM: class M
  let cV: class V
  let cW: class W
  let c.0: class .0.
  let vm: setvar m
  let vw: setvar w
  let vg: setvar g
  let vx: setvar x
  let cF: class F
  assume sitgval.b: |- B = ( Base ` W )
  assume sitgval.j: |- J = ( TopOpen ` W )
  assume sitgval.s: |- S = ( sigaGen ` J )
  assume sitgval.0: |- .0. = ( 0g ` W )
  assume sitgval.x: |- .x. = ( .s ` W )
  assume sitgval.h: |- H = ( RRHom ` ( Scalar ` W ) )
  assume sitgval.1: |- ( ph -> W e. V )
  assume sitgval.2: |- ( ph -> M e. U. ran measures )
  assume sitgf.1: |- ( ( ph /\ f e. dom ( W sitg M ) ) -> ( ( W sitg M ) ` f ) e. B )

  disjoint f ph
  disjoint B f
  disjoint H f
  disjoint M f
  disjoint S f
  disjoint W f
  disjoint .0. f
  disjoint .x. f
  disjoint f m
  disjoint f w
  disjoint m w
  disjoint B m
  disjoint B w
  disjoint f g
  disjoint f x
  disjoint F f
  disjoint g x
  disjoint F g
  disjoint F x
  disjoint H m
  disjoint H w
  disjoint g m
  disjoint g w
  disjoint M g
  disjoint m x
  disjoint M m
  disjoint w x
  disjoint M w
  disjoint M x
  disjoint S g
  disjoint S m
  disjoint S w
  disjoint W g
  disjoint W m
  disjoint W w
  disjoint W x
  disjoint .0. g
  disjoint .0. m
  disjoint .0. w
  disjoint .0. x
  disjoint .x. m
  disjoint .x. w
  assert |- ( ph -> ( W sitg M ) : dom ( W sitg M ) --> B )

  proof
    wph
    cW
    cM
    csitg
    co
    #
    @0
    cdm
    #
    wfn
    #
    @0
    crn
    cB
    wss
    #
    @1
    cB
    @0
    wf
    wph
    @0
    wfun
    #
    @2
    wph
    @4
    vf
    vg
    cv
    #
    crn
    #
    cfn
    wcel
    @5
    ccnv
    vx
    cv
    #
    csn
    #
    cima
    cM
    cfv
    cc0
    cpnf
    cico
    co
    wcel
    vx
    @6
    c.0
    csn
    #
    cdif
    wral
    wa
    vg
    cM
    cdm
    cS
    cmbfm
    co
    crab
    #
    cW
    vx
    vf
    cv
    #
    crn
    @9
    cdif
    @11
    ccnv
    @8
    cima
    cM
    cfv
    cH
    cfv
    @7
    c.x
    co
    cmpt
    cgsu
    co
    #
    cmpt
    #
    wfun
    vf
    @10
    @12
    funmpt
    wph
    @0
    @13
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
    funeqd
    mpbiri
    @0
    funfn
    sylib
    #
    wph
    @2
    @11
    @0
    cfv
    cB
    wcel
    #
    vf
    @1
    wral
    @3
    @14
    wph
    @15
    vf
    @1
    sitgf.1
    ralrimiva
    vf
    @1
    cB
    @0
    fnfvrnss
    syl2anc
    @1
    cB
    @0
    df-f
    sylanbrc
end
