include "cn0.mm"
include "wss.mm"
include "c0.mm"
include "csad.mm"
include "co.mm"
include "wceq.mm"
include "0ss.mm"
include "sadcom.mm"
include "mpan.mm"
include "sadid1.mm"
include "eqtrd.mm"

theorem sadid2
  let cA: class A
  let vc: setvar c
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let cB: class B
  let cN: class N


  assert |- ( A C_ NN0 -> ( (/) sadd A ) = A )

  proof
    cA
    cn0
    wss
    #
    c0
    cA
    csad
    co
    #
    cA
    c0
    csad
    co
    #
    cA
    c0
    cn0
    wss
    @0
    @1
    @2
    wceq
    cn0
    0ss
    c0
    cA
    sadcom
    mpan
    cA
    sadid1
    eqtrd
end
