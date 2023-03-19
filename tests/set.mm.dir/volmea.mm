include "cvol.mm"
include "cdm.mm"
include "csalg.mm"
include "wcel.mm"
include "dmvolsal.mm"
include "a1i.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wf.mm"
include "volf.mm"
include "c0.mm"
include "cfv.mm"
include "wceq.mm"
include "vol0.mm"
include "cn.mm"
include "cv.mm"
include "wdisj.mm"
include "w3a.mm"
include "ciun.mm"
include "cmpt.mm"
include "csumge0.mm"
include "simp1.mm"
include "simp2.mm"
include "fveq2.mm"
include "cbvdisjv.mm"
include "biimpri.mm"
include "3ad2ant3.mm"
include "biimpi.mm"
include "voliunsge0.mm"
include "syl3anc.mm"
include "ismeannd.mm"

theorem volmea
  let wph: wff ph
  let ve: setvar e
  let vm: setvar m
  let vn: setvar n
  let vk: setvar k
  let vx: setvar x


  assert |- ( ph -> vol e. Meas )

  proof
    wph
    cvol
    cdm
    #
    ve
    vn
    cvol
    @0
    csalg
    wcel
    wph
    dmvolsal
    a1i
    @0
    cc0
    cpnf
    cicc
    co
    cvol
    wf
    wph
    volf
    a1i
    c0
    cvol
    cfv
    cc0
    wceq
    wph
    vol0
    a1i
    wph
    cn
    @0
    ve
    cv
    #
    wf
    #
    vn
    cn
    vn
    cv
    #
    @1
    cfv
    #
    wdisj
    #
    w3a
    wph
    @2
    vm
    cn
    vm
    cv
    #
    @1
    cfv
    #
    wdisj
    #
    vn
    cn
    @4
    ciun
    cvol
    cfv
    vn
    cn
    @4
    cvol
    cfv
    cmpt
    csumge0
    cfv
    wceq
    wph
    @2
    @5
    simp1
    wph
    @2
    @5
    simp2
    @5
    wph
    @8
    @2
    @8
    @5
    vm
    vn
    cn
    @7
    @4
    @6
    @3
    @1
    fveq2
    cbvdisjv
    #
    biimpri
    3ad2ant3
    wph
    @2
    @8
    w3a
    vn
    @1
    wph
    @2
    @8
    simp2
    @8
    wph
    @5
    @2
    @8
    @5
    @9
    biimpi
    3ad2ant3
    voliunsge0
    syl3anc
    ismeannd
end
