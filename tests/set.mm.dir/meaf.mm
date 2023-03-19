include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wf.mm"
include "cdm.mm"
include "csalg.mm"
include "wcel.mm"
include "c0.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
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
include "simpld.mm"
include "simplld.mm"
include "a1i.mm"
include "feq2d.mm"
include "mpbird.mm"

theorem meaf
  let wph: wff ph
  let cS: class S
  let cM: class M
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k
  assume meaf.m: |- ( ph -> M e. Meas )
  assume meaf.s: |- S = dom M


  assert |- ( ph -> M : S --> ( 0 [,] +oo ) )

  proof
    wph
    cS
    cc0
    cpnf
    cicc
    co
    #
    cM
    wf
    cM
    cdm
    #
    @0
    cM
    wf
    #
    wph
    @2
    @1
    csalg
    wcel
    #
    c0
    cM
    cfv
    cc0
    wceq
    #
    wph
    @2
    @3
    wa
    @4
    wa
    #
    vx
    cv
    #
    com
    cdom
    wbr
    vy
    @6
    vy
    cv
    wdisj
    wa
    @6
    cuni
    cM
    cfv
    cM
    @6
    cres
    csumge0
    cfv
    wceq
    wi
    vx
    @1
    cpw
    wral
    #
    wph
    cM
    cmea
    wcel
    @5
    @7
    wa
    meaf.m
    vx
    vy
    cM
    ismea
    sylib
    simpld
    simplld
    wph
    cS
    @1
    @0
    cM
    cS
    @1
    wceq
    wph
    meaf.s
    a1i
    feq2d
    mpbird
end
