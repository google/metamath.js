include "cc.mm"
include "cz.mm"
include "cn.mm"
include "cdif.mm"
include "wcel.mm"
include "wn.mm"
include "wa.mm"
include "cigam.mm"
include "cfv.mm"
include "c1.mm"
include "cgam.mm"
include "cdiv.mm"
include "co.mm"
include "wceq.mm"
include "eldif.mm"
include "cc0.mm"
include "cif.mm"
include "igamval.mm"
include "iffalse.mm"
include "sylan9eq.mm"
include "sylbi.mm"

theorem igamgam
  let cA: class A
  let vk: setvar k
  let vn: setvar n
  let vr: setvar r
  let vx: setvar x


  assert |- ( A e. ( CC \ ( ZZ \ NN ) ) -> ( 1/_G ` A ) = ( 1 / ( _G ` A ) ) )

  proof
    cA
    cc
    cz
    cn
    cdif
    #
    cdif
    wcel
    cA
    cc
    wcel
    #
    cA
    @0
    wcel
    #
    wn
    #
    wa
    cA
    cigam
    cfv
    #
    c1
    cA
    cgam
    cfv
    cdiv
    co
    #
    wceq
    cA
    cc
    @0
    eldif
    @1
    @3
    @4
    @2
    cc0
    @5
    cif
    @5
    cA
    igamval
    @2
    cc0
    @5
    iffalse
    sylan9eq
    sylbi
end
