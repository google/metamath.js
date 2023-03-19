include "cioo.mm"
include "co.mm"
include "cixp.mm"
include "cico.mm"
include "wss.mm"
include "wtru.mm"
include "nftru.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "ioossico.mm"
include "a1i.mm"
include "ixpssixp.mm"
include "trud.mm"

theorem ioosshoi
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cX: class X
  let vx: setvar x


  assert |- X_ k e. X ( A (,) B ) C_ X_ k e. X ( A [,) B )

  proof
    vk
    cX
    cA
    cB
    cioo
    co
    #
    cixp
    vk
    cX
    cA
    cB
    cico
    co
    #
    cixp
    wss
    wtru
    vk
    cX
    @0
    @1
    vk
    nftru
    @0
    @1
    wss
    wtru
    vk
    cv
    cX
    wcel
    wa
    cA
    cB
    ioossico
    a1i
    ixpssixp
    trud
end
