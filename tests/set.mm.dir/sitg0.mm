include "cdm.mm"
include "cuni.mm"
include "csn.mm"
include "cxp.mm"
include "csitg.mm"
include "co.mm"
include "cfv.mm"
include "crn.mm"
include "cdif.mm"
include "ccnv.mm"
include "cv.mm"
include "cima.mm"
include "cmpt.mm"
include "cgsu.mm"
include "sibf0.mm"
include "sitgfval.mm"
include "c0.mm"
include "wceq.mm"
include "wss.mm"
include "rnxpss.mm"
include "ssdif0.mm"
include "mpbi.mm"
include "mpteq1.mm"
include "ax-mp.mm"
include "mpt0.mm"
include "eqtri.mm"
include "oveq2i.mm"
include "gsum0.mm"
include "syl6eq.mm"

theorem sitg0
  let wph: wff ph
  let cB: class B
  let cS: class S
  let c.x: class .x.
  let cH: class H
  let cJ: class J
  let cM: class M
  let cV: class V
  let cW: class W
  let c.0: class .0.
  let vx: setvar x
  let vf: setvar f
  let vm: setvar m
  let vw: setvar w
  let vg: setvar g
  let cF: class F
  assume sitgval.b: |- B = ( Base ` W )
  assume sitgval.j: |- J = ( TopOpen ` W )
  assume sitgval.s: |- S = ( sigaGen ` J )
  assume sitgval.0: |- .0. = ( 0g ` W )
  assume sitgval.x: |- .x. = ( .s ` W )
  assume sitgval.h: |- H = ( RRHom ` ( Scalar ` W ) )
  assume sitgval.1: |- ( ph -> W e. V )
  assume sitgval.2: |- ( ph -> M e. U. ran measures )
  assume sitg0.1: |- ( ph -> W e. TopSp )
  assume sitg0.2: |- ( ph -> W e. Mnd )


  assert |- ( ph -> ( ( W sitg M ) ` ( U. dom M X. { .0. } ) ) = .0. )

  proof
    wph
    cM
    cdm
    cuni
    #
    c.0
    csn
    #
    cxp
    #
    cW
    cM
    csitg
    co
    cfv
    cW
    vx
    @2
    crn
    #
    @1
    cdif
    #
    @2
    ccnv
    vx
    cv
    #
    csn
    cima
    cM
    cfv
    cH
    cfv
    @5
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    #
    c.0
    wph
    vx
    cB
    cS
    c.x
    @2
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
    wph
    cB
    cS
    c.x
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
    sitg0.1
    sitg0.2
    sibf0
    sitgfval
    @8
    cW
    c0
    cgsu
    co
    c.0
    @7
    c0
    cW
    cgsu
    @7
    vx
    c0
    @6
    cmpt
    #
    c0
    @4
    c0
    wceq
    #
    @7
    @9
    wceq
    @3
    @1
    wss
    @10
    @0
    @1
    rnxpss
    @3
    @1
    ssdif0
    mpbi
    vx
    @4
    c0
    @6
    mpteq1
    ax-mp
    vx
    @6
    mpt0
    eqtri
    oveq2i
    cW
    c.0
    sitgval.0
    gsum0
    eqtri
    syl6eq
end
