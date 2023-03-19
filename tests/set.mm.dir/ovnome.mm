include "covoln.mm"
include "cfv.mm"
include "cvv.mm"
include "cr.mm"
include "cmap.mm"
include "co.mm"
include "ovexd.mm"
include "ovnf.mm"
include "ovn0.mm"
include "cv.mm"
include "wss.mm"
include "w3a.mm"
include "cfn.mm"
include "wcel.mm"
include "3ad2ant1.mm"
include "simp3.mm"
include "simp2.mm"
include "ovnssle.mm"
include "cn.mm"
include "cpw.mm"
include "wf.mm"
include "wa.mm"
include "adantr.mm"
include "simpr.mm"
include "ovnsubadd.mm"
include "isomennd.mm"

theorem ovnome
  let wph: wff ph
  let cX: class X
  let va: setvar a
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k
  assume ovnome.1: |- ( ph -> X e. Fin )


  assert |- ( ph -> ( voln* ` X ) e. OutMeas )

  proof
    wph
    vx
    vy
    vn
    cX
    covoln
    cfv
    cvv
    cr
    cX
    cmap
    co
    #
    va
    wph
    cr
    cX
    cmap
    ovexd
    wph
    cX
    ovnome.1
    ovnf
    wph
    cX
    ovnome.1
    ovn0
    wph
    vx
    cv
    #
    @0
    wss
    #
    vy
    cv
    #
    @1
    wss
    #
    w3a
    @3
    @1
    cX
    wph
    @2
    cX
    cfn
    wcel
    #
    @4
    ovnome.1
    3ad2ant1
    wph
    @2
    @4
    simp3
    wph
    @2
    @4
    simp2
    ovnssle
    wph
    cn
    @0
    cpw
    va
    cv
    #
    wf
    #
    wa
    @6
    vn
    cX
    wph
    @5
    @7
    ovnome.1
    adantr
    wph
    @7
    simpr
    ovnsubadd
    isomennd
end
