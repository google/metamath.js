include "cdm.mm"
include "csalg.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wf.mm"
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
include "simplld.mm"
include "simprd.mm"
include "syl5eqel.mm"

theorem dmmeasal
  let wph: wff ph
  let cS: class S
  let cM: class M
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k
  assume dmmeasal.m: |- ( ph -> M e. Meas )
  assume dmmeasal.s: |- S = dom M


  assert |- ( ph -> S e. SAlg )

  proof
    wph
    cS
    cM
    cdm
    #
    csalg
    dmmeasal.s
    wph
    @0
    cc0
    cpnf
    cicc
    co
    cM
    wf
    #
    @0
    csalg
    wcel
    #
    wph
    @1
    @2
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
    @5
    vy
    cv
    wdisj
    wa
    @5
    cuni
    cM
    cfv
    cM
    @5
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
    @3
    @4
    wa
    @6
    wa
    dmmeasal.m
    vx
    vy
    cM
    ismea
    sylib
    simplld
    simprd
    syl5eqel
end
