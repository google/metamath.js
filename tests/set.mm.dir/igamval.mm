include "cv.mm"
include "cz.mm"
include "cn.mm"
include "cdif.mm"
include "wcel.mm"
include "cc0.mm"
include "c1.mm"
include "cgam.mm"
include "cfv.mm"
include "cdiv.mm"
include "co.mm"
include "cif.mm"
include "cc.mm"
include "cigam.mm"
include "wceq.mm"
include "eleq1.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "ifbieq2d.mm"
include "df-igam.mm"
include "c0ex.mm"
include "ovex.mm"
include "ifex.mm"
include "fvmpt.mm"

theorem igamval
  let cA: class A
  let vk: setvar k
  let vn: setvar n
  let vr: setvar r
  let vx: setvar x


  assert |- ( A e. CC -> ( 1/_G ` A ) = if ( A e. ( ZZ \ NN ) , 0 , ( 1 / ( _G ` A ) ) ) )

  proof
    vx
    cA
    vx
    cv
    #
    cz
    cn
    cdif
    #
    wcel
    #
    cc0
    c1
    @0
    cgam
    cfv
    #
    cdiv
    co
    #
    cif
    cA
    @1
    wcel
    #
    cc0
    c1
    cA
    cgam
    cfv
    #
    cdiv
    co
    #
    cif
    cc
    cigam
    @0
    cA
    wceq
    #
    @2
    @5
    @4
    @7
    cc0
    @0
    cA
    @1
    eleq1
    @8
    @3
    @6
    c1
    cdiv
    @0
    cA
    cgam
    fveq2
    oveq2d
    ifbieq2d
    vx
    df-igam
    @5
    cc0
    @7
    c0ex
    c1
    @6
    cdiv
    ovex
    ifex
    fvmpt
end
