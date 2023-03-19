include "cn0.mm"
include "wss.mm"
include "wa.mm"
include "csmu.mm"
include "co.mm"
include "cv.mm"
include "c1.mm"
include "caddc.mm"
include "cpw.mm"
include "wcel.mm"
include "cmin.mm"
include "crab.mm"
include "csad.mm"
include "cmpt2.mm"
include "cc0.mm"
include "wceq.mm"
include "c0.mm"
include "cif.mm"
include "cmpt.mm"
include "cseq.mm"
include "cfv.mm"
include "simpl.mm"
include "simpr.mm"
include "eqid.mm"
include "smufval.mm"
include "ssrab2.mm"
include "syl6eqss.mm"

theorem smucl
  let cA: class A
  let cB: class B
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vp: setvar p
  let vx: setvar x
  let wph: wff ph


  assert |- ( ( A C_ NN0 /\ B C_ NN0 ) -> ( A smul B ) C_ NN0 )

  proof
    cA
    cn0
    wss
    #
    cB
    cn0
    wss
    #
    wa
    #
    cA
    cB
    csmu
    co
    vk
    cv
    #
    @3
    c1
    caddc
    co
    vp
    vm
    cn0
    cpw
    cn0
    vp
    cv
    vm
    cv
    #
    cA
    wcel
    vn
    cv
    #
    @4
    cmin
    co
    cB
    wcel
    wa
    vn
    cn0
    crab
    csad
    co
    cmpt2
    vn
    cn0
    @5
    cc0
    wceq
    c0
    @5
    c1
    cmin
    co
    cif
    cmpt
    cc0
    cseq
    #
    cfv
    wcel
    #
    vk
    cn0
    crab
    cn0
    @2
    cA
    cB
    @6
    vk
    vm
    vn
    vp
    @0
    @1
    simpl
    @0
    @1
    simpr
    @6
    eqid
    smufval
    @7
    vk
    cn0
    ssrab2
    syl6eqss
end
