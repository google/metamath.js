include "cz.mm"
include "cn.mm"
include "cdif.mm"
include "wcel.mm"
include "cigam.mm"
include "cfv.mm"
include "cc0.mm"
include "c1.mm"
include "cgam.mm"
include "cdiv.mm"
include "co.mm"
include "cif.mm"
include "cc.mm"
include "wceq.mm"
include "eldifi.mm"
include "zcnd.mm"
include "igamval.mm"
include "syl.mm"
include "iftrue.mm"
include "eqtrd.mm"

theorem igamz
  let cA: class A
  let vk: setvar k
  let vn: setvar n
  let vr: setvar r
  let vx: setvar x


  assert |- ( A e. ( ZZ \ NN ) -> ( 1/_G ` A ) = 0 )

  proof
    cA
    cz
    cn
    cdif
    wcel
    #
    cA
    cigam
    cfv
    #
    @0
    cc0
    c1
    cA
    cgam
    cfv
    cdiv
    co
    #
    cif
    #
    cc0
    @0
    cA
    cc
    wcel
    @1
    @3
    wceq
    @0
    cA
    cA
    cz
    cn
    eldifi
    zcnd
    cA
    igamval
    syl
    @0
    cc0
    @2
    iftrue
    eqtrd
end
