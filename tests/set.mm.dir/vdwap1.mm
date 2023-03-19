include "cn.mm"
include "wcel.mm"
include "wa.mm"
include "c1.mm"
include "cvdwa.mm"
include "cfv.mm"
include "co.mm"
include "csn.mm"
include "caddc.mm"
include "cc0.mm"
include "cun.mm"
include "1e0p1.mm"
include "fveq2i.mm"
include "oveqi.mm"
include "cn0.mm"
include "wceq.mm"
include "0nn0.mm"
include "vdwapun.mm"
include "mp3an1.mm"
include "syl5eq.mm"
include "c0.mm"
include "nnaddcl.mm"
include "vdwap0.mm"
include "sylancom.mm"
include "uneq2d.mm"
include "un0.mm"
include "syl6eq.mm"
include "eqtrd.mm"

theorem vdwap1
  let cA: class A
  let cD: class D
  let va: setvar a
  let vd: setvar d
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let vk: setvar k
  let cK: class K
  let cX: class X


  assert |- ( ( A e. NN /\ D e. NN ) -> ( A ( AP ` 1 ) D ) = { A } )

  proof
    cA
    cn
    wcel
    #
    cD
    cn
    wcel
    #
    wa
    #
    cA
    cD
    c1
    cvdwa
    cfv
    #
    co
    #
    cA
    csn
    #
    cA
    cD
    caddc
    co
    #
    cD
    cc0
    cvdwa
    cfv
    co
    #
    cun
    #
    @5
    @2
    @4
    cA
    cD
    cc0
    c1
    caddc
    co
    #
    cvdwa
    cfv
    #
    co
    #
    @8
    @3
    @10
    cA
    cD
    c1
    @9
    cvdwa
    1e0p1
    fveq2i
    oveqi
    cc0
    cn0
    wcel
    @0
    @1
    @11
    @8
    wceq
    0nn0
    cA
    cD
    cc0
    vdwapun
    mp3an1
    syl5eq
    @2
    @8
    @5
    c0
    cun
    @5
    @2
    @7
    c0
    @5
    @0
    @1
    @6
    cn
    wcel
    @7
    c0
    wceq
    cA
    cD
    nnaddcl
    @6
    cD
    vdwap0
    sylancom
    uneq2d
    @5
    un0
    syl6eq
    eqtrd
end
