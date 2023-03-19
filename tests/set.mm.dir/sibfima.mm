include "ccnv.mm"
include "cv.mm"
include "csn.mm"
include "cima.mm"
include "cfv.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "wcel.mm"
include "crn.mm"
include "cdif.mm"
include "wral.mm"
include "cdm.mm"
include "cmbfm.mm"
include "cfn.mm"
include "csitg.mm"
include "w3a.mm"
include "issibf.mm"
include "mpbid.mm"
include "simp3d.mm"
include "wceq.mm"
include "sneq.mm"
include "imaeq2d.mm"
include "fveq2d.mm"
include "eleq1d.mm"
include "rspcv.mm"
include "mpan9.mm"

theorem sibfima
  let wph: wff ph
  let cA: class A
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
  let vx: setvar x
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


  assert |- ( ( ph /\ A e. ( ran F \ { .0. } ) ) -> ( M ` ( `' F " { A } ) ) e. ( 0 [,) +oo ) )

  proof
    wph
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
    cF
    crn
    #
    c.0
    csn
    cdif
    #
    wral
    #
    cA
    @8
    wcel
    @0
    cA
    csn
    #
    cima
    #
    cM
    cfv
    #
    @5
    wcel
    #
    wph
    cF
    cM
    cdm
    cS
    cmbfm
    co
    wcel
    #
    @7
    cfn
    wcel
    #
    @9
    wph
    cF
    cW
    cM
    csitg
    co
    cdm
    wcel
    @14
    @15
    @9
    w3a
    sibfmbl.1
    wph
    vx
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
    issibf
    mpbid
    simp3d
    @6
    @13
    vx
    cA
    @8
    @1
    cA
    wceq
    #
    @4
    @12
    @5
    @16
    @3
    @11
    cM
    @16
    @2
    @10
    @0
    @1
    cA
    sneq
    imaeq2d
    fveq2d
    eleq1d
    rspcv
    mpan9
end
