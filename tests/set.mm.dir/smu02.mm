include "cn0.mm"
include "wss.mm"
include "c0.mm"
include "0ss.mm"
include "a1i.mm"
include "id.mm"
include "cv.mm"
include "wcel.mm"
include "cmin.mm"
include "co.mm"
include "wa.mm"
include "wn.mm"
include "noel.mm"
include "intnanr.mm"
include "smu01lem.mm"

theorem smu02
  let cA: class A
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let vp: setvar p
  let vx: setvar x
  let cB: class B
  let wph: wff ph


  assert |- ( A C_ NN0 -> ( (/) smul A ) = (/) )

  proof
    cA
    cn0
    wss
    #
    c0
    cA
    vk
    vn
    c0
    cn0
    wss
    @0
    cn0
    0ss
    a1i
    @0
    id
    vk
    cv
    #
    c0
    wcel
    #
    vn
    cv
    #
    @1
    cmin
    co
    cA
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
    @2
    @4
    @1
    noel
    intnanr
    a1i
    smu01lem
end
