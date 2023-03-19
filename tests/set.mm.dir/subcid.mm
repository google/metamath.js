include "ccid.mm"
include "cfv.mm"
include "cv.mm"
include "cvv.mm"
include "ccat.mm"
include "wcel.mm"
include "cmpt.mm"
include "wceq.mm"
include "subccatid.mm"
include "simprd.mm"
include "wa.mm"
include "simpr.mm"
include "fveq2d.mm"
include "fvexd.mm"
include "fvmptd.mm"
include "eqcomd.mm"

theorem subcid
  let wph: wff ph
  let cC: class C
  let cD: class D
  let cS: class S
  let c.1: class .1.
  let cJ: class J
  let cX: class X
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume subccat.1: |- D = ( C |`cat J )
  assume subccat.j: |- ( ph -> J e. ( Subcat ` C ) )
  assume subccatid.1: |- ( ph -> J Fn ( S X. S ) )
  assume subccatid.2: |- .1. = ( Id ` C )
  assume subcid.x: |- ( ph -> X e. S )


  assert |- ( ph -> ( .1. ` X ) = ( ( Id ` D ) ` X ) )

  proof
    wph
    cX
    cD
    ccid
    cfv
    #
    cfv
    cX
    c.1
    cfv
    #
    wph
    vx
    cX
    vx
    cv
    #
    c.1
    cfv
    #
    @1
    cS
    @0
    cvv
    wph
    cD
    ccat
    wcel
    @0
    vx
    cS
    @3
    cmpt
    wceq
    wph
    vx
    cC
    cD
    cS
    c.1
    cJ
    subccat.1
    subccat.j
    subccatid.1
    subccatid.2
    subccatid
    simprd
    wph
    @2
    cX
    wceq
    #
    wa
    @2
    cX
    c.1
    wph
    @4
    simpr
    fveq2d
    subcid.x
    wph
    cX
    c.1
    fvexd
    fvmptd
    eqcomd
end
