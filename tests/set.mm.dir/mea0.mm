include "cdm.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wf.mm"
include "csalg.mm"
include "wcel.mm"
include "wa.mm"
include "c0.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wdisj.mm"
include "cuni.mm"
include "cres.mm"
include "csumge0.mm"
include "wi.mm"
include "cpw.mm"
include "wral.mm"
include "cmea.mm"
include "ismea.mm"
include "sylib.mm"
include "simplrd.mm"

theorem mea0
  let wph: wff ph
  let cM: class M
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k
  assume mea0.1: |- ( ph -> M e. Meas )


  assert |- ( ph -> ( M ` (/) ) = 0 )

  proof
    wph
    cM
    cdm
    #
    cc0
    cpnf
    cicc
    co
    cM
    wf
    @0
    csalg
    wcel
    wa
    #
    c0
    cM
    cfv
    cc0
    wceq
    #
    vx
    cv
    #
    com
    cdom
    wbr
    vy
    @3
    vy
    cv
    wdisj
    wa
    @3
    cuni
    cM
    cfv
    cM
    @3
    cres
    csumge0
    cfv
    wceq
    wi
    vx
    @0
    cpw
    wral
    #
    wph
    cM
    cmea
    wcel
    @1
    @2
    wa
    @4
    wa
    mea0.1
    vx
    vy
    cM
    ismea
    sylib
    simplrd
end
