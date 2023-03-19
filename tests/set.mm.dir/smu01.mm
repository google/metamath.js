include "cn0.mm"
include "wss.mm"
include "c0.mm"
include "id.mm"
include "0ss.mm"
include "a1i.mm"
include "cv.mm"
include "wcel.mm"
include "cmin.mm"
include "co.mm"
include "wa.mm"
include "wn.mm"
include "noel.mm"
include "intnan.mm"
include "smu01lem.mm"

theorem smu01
  let cA: class A
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vp: setvar p
  let vx: setvar x
  let cB: class B
  let wph: wff ph


  assert |- ( A C_ NN0 -> ( A smul (/) ) = (/) )

  proof
    cA
    cn0
    wss
    #
    cA
    c0
    vk
    vn
    @0
    id
    c0
    cn0
    wss
    @0
    cn0
    0ss
    a1i
    vk
    cv
    #
    cA
    wcel
    #
    vn
    cv
    #
    @1
    cmin
    co
    #
    c0
    wcel
    #
    wa
    wn
    @0
    @1
    cn0
    wcel
    @3
    cn0
    wcel
    wa
    wa
    @5
    @2
    @4
    noel
    intnan
    a1i
    smu01lem
end
