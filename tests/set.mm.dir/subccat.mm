include "ccat.mm"
include "wcel.mm"
include "ccid.mm"
include "cfv.mm"
include "cdm.mm"
include "cv.mm"
include "cmpt.mm"
include "wceq.mm"
include "eqidd.mm"
include "subcfn.mm"
include "eqid.mm"
include "subccatid.mm"
include "simpld.mm"

theorem subccat
  let wph: wff ph
  let cC: class C
  let cD: class D
  let cJ: class J
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cX: class X
  let c.1: class .1.
  let cS: class S
  assume subccat.1: |- D = ( C |`cat J )
  assume subccat.j: |- ( ph -> J e. ( Subcat ` C ) )


  assert |- ( ph -> D e. Cat )

  proof
    wph
    cD
    ccat
    wcel
    cD
    ccid
    cfv
    vx
    cJ
    cdm
    cdm
    #
    vx
    cv
    cC
    ccid
    cfv
    #
    cfv
    cmpt
    wceq
    wph
    vx
    cC
    cD
    @0
    @1
    cJ
    subccat.1
    subccat.j
    wph
    cC
    @0
    cJ
    subccat.j
    wph
    @0
    eqidd
    subcfn
    @1
    eqid
    subccatid
    simpld
end
