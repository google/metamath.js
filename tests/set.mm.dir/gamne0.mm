include "cc.mm"
include "cz.mm"
include "cn.mm"
include "cdif.mm"
include "wcel.mm"
include "clgam.mm"
include "cfv.mm"
include "ce.mm"
include "cgam.mm"
include "cc0.mm"
include "eflgam.mm"
include "wne.mm"
include "lgamcl.mm"
include "efne0.mm"
include "syl.mm"
include "eqnetrrd.mm"

theorem gamne0
  let cA: class A
  let vk: setvar k
  let vn: setvar n
  let vr: setvar r
  let vx: setvar x


  assert |- ( A e. ( CC \ ( ZZ \ NN ) ) -> ( _G ` A ) =/= 0 )

  proof
    cA
    cc
    cz
    cn
    cdif
    cdif
    wcel
    #
    cA
    clgam
    cfv
    #
    ce
    cfv
    #
    cA
    cgam
    cfv
    cc0
    cA
    eflgam
    @0
    @1
    cc
    wcel
    @2
    cc0
    wne
    cA
    lgamcl
    @1
    efne0
    syl
    eqnetrrd
end
