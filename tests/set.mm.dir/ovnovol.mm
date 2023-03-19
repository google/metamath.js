include "csn.mm"
include "cmap.mm"
include "co.mm"
include "cn.mm"
include "cv.mm"
include "cico.mm"
include "cfv.mm"
include "ccom.mm"
include "cixp.mm"
include "ciun.mm"
include "wss.mm"
include "cvol.mm"
include "cprod.mm"
include "cmpt.mm"
include "csumge0.mm"
include "wceq.mm"
include "wa.mm"
include "cr.mm"
include "cxp.mm"
include "wrex.mm"
include "cxr.mm"
include "crab.mm"
include "crn.mm"
include "cuni.mm"
include "eqid.mm"
include "eqeq1.mm"
include "anbi2d.mm"
include "rexbidv.mm"
include "cbvrabv.mm"
include "ovnovollem3.mm"

theorem ovnovol
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cV: class V
  let vf: setvar f
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vz: setvar z
  let vw: setvar w
  let vx: setvar x
  assume ovnovol.a: |- ( ph -> A e. V )
  assume ovnovol.b: |- ( ph -> B C_ RR )


  assert |- ( ph -> ( ( voln* ` { A } ) ` ( B ^m { A } ) ) = ( vol* ` B ) )

  proof
    wph
    vz
    cA
    cB
    vf
    vi
    vj
    vk
    cB
    cA
    csn
    #
    cmap
    co
    vj
    cn
    vk
    @0
    vk
    cv
    cico
    vj
    cv
    vi
    cv
    cfv
    ccom
    cfv
    #
    cixp
    ciun
    wss
    vz
    cv
    #
    vj
    cn
    @0
    @1
    cvol
    cfv
    vk
    cprod
    cmpt
    csumge0
    cfv
    wceq
    wa
    vi
    cr
    cr
    cxp
    #
    @0
    cmap
    co
    cn
    cmap
    co
    wrex
    vz
    cxr
    crab
    #
    cB
    cico
    vf
    cv
    #
    ccom
    crn
    cuni
    wss
    #
    vw
    cv
    #
    cvol
    cico
    ccom
    @5
    ccom
    csumge0
    cfv
    #
    wceq
    #
    wa
    #
    vf
    @3
    cn
    cmap
    co
    #
    wrex
    #
    vw
    cxr
    crab
    cV
    ovnovol.a
    ovnovol.b
    @4
    eqid
    @12
    @6
    @2
    @8
    wceq
    #
    wa
    #
    vf
    @11
    wrex
    vw
    vz
    cxr
    @7
    @2
    wceq
    #
    @10
    @14
    vf
    @11
    @15
    @9
    @13
    @6
    @7
    @2
    @8
    eqeq1
    anbi2d
    rexbidv
    cbvrabv
    ovnovollem3
end
