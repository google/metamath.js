include "cn0.mm"
include "wss.mm"
include "c0.mm"
include "csad.mm"
include "co.mm"
include "cun.mm"
include "id.mm"
include "0ss.mm"
include "a1i.mm"
include "cin.mm"
include "wceq.mm"
include "in0.mm"
include "saddisj.mm"
include "un0.mm"
include "syl6eq.mm"

theorem sadid1
  let cA: class A
  let vc: setvar c
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let cB: class B
  let cN: class N


  assert |- ( A C_ NN0 -> ( A sadd (/) ) = A )

  proof
    cA
    cn0
    wss
    #
    cA
    c0
    csad
    co
    cA
    c0
    cun
    cA
    @0
    cA
    c0
    @0
    id
    c0
    cn0
    wss
    @0
    cn0
    0ss
    a1i
    cA
    c0
    cin
    c0
    wceq
    @0
    cA
    in0
    a1i
    saddisj
    cA
    un0
    syl6eq
end
