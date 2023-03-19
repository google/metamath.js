include "csumge0.mm"
include "cfv.mm"
include "cpnf.mm"
include "crn.mm"
include "wcel.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "cv.mm"
include "csu.mm"
include "cmpt.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cif.mm"
include "sge0vald.mm"
include "iftrued.mm"
include "eqtrd.mm"

theorem sge0pnfval
  let wph: wff ph
  let cF: class F
  let cV: class V
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k
  assume sge0pnfval.x: |- ( ph -> X e. V )
  assume sge0pnfval.f: |- ( ph -> F : X --> ( 0 [,] +oo ) )
  assume sge0pnfval.pnf: |- ( ph -> +oo e. ran F )


  assert |- ( ph -> ( sum^ ` F ) = +oo )

  proof
    wph
    cF
    csumge0
    cfv
    cpnf
    cF
    crn
    wcel
    #
    cpnf
    vx
    cX
    cpw
    cfn
    cin
    vx
    cv
    vy
    cv
    cF
    cfv
    vy
    csu
    cmpt
    crn
    cxr
    clt
    csup
    #
    cif
    cpnf
    wph
    vx
    vy
    cF
    cV
    cX
    sge0pnfval.x
    sge0pnfval.f
    sge0vald
    wph
    @0
    cpnf
    @1
    sge0pnfval.pnf
    iftrued
    eqtrd
end
