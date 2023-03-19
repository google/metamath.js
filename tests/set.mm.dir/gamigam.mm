include "cc.mm"
include "cz.mm"
include "cn.mm"
include "cdif.mm"
include "wcel.mm"
include "c1.mm"
include "cigam.mm"
include "cfv.mm"
include "cdiv.mm"
include "co.mm"
include "cgam.mm"
include "igamgam.mm"
include "oveq2d.mm"
include "gamcl.mm"
include "gamne0.mm"
include "recrecd.mm"
include "eqtr2d.mm"

theorem gamigam
  let cA: class A
  let vk: setvar k
  let vn: setvar n
  let vr: setvar r
  let vx: setvar x


  assert |- ( A e. ( CC \ ( ZZ \ NN ) ) -> ( _G ` A ) = ( 1 / ( 1/_G ` A ) ) )

  proof
    cA
    cc
    cz
    cn
    cdif
    cdif
    wcel
    #
    c1
    cA
    cigam
    cfv
    #
    cdiv
    co
    c1
    c1
    cA
    cgam
    cfv
    #
    cdiv
    co
    #
    cdiv
    co
    @2
    @0
    @1
    @3
    c1
    cdiv
    cA
    igamgam
    oveq2d
    @0
    @2
    cA
    gamcl
    cA
    gamne0
    recrecd
    eqtr2d
end
