include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "c2.mm"
include "cmul.mm"
include "co.mm"
include "c1.mm"
include "caddc.mm"
include "cdiv.mm"
include "wn.mm"
include "wne.mm"
include "halfnz.mm"
include "wceq.mm"
include "cmin.mm"
include "cc.mm"
include "2cn.mm"
include "zcn.mm"
include "adantr.mm"
include "mulcl.mm"
include "sylancr.mm"
include "adantl.mm"
include "1cnd.mm"
include "subaddd.mm"
include "a1i.mm"
include "subdid.mm"
include "oveq1d.mm"
include "zsubcl.mm"
include "syl.mm"
include "cc0.mm"
include "2ne0.mm"
include "divcan3d.mm"
include "eqtr3d.mm"
include "eqeltrd.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "syl5ibcom.mm"
include "sylbird.mm"
include "necon3bd.mm"
include "mpi.mm"
include "necomd.mm"

theorem zneo
  let cA: class A
  let cB: class B


  assert |- ( ( A e. ZZ /\ B e. ZZ ) -> ( 2 x. A ) =/= ( ( 2 x. B ) + 1 ) )

  proof
    cA
    cz
    wcel
    #
    cB
    cz
    wcel
    #
    wa
    #
    c2
    cB
    cmul
    co
    #
    c1
    caddc
    co
    #
    c2
    cA
    cmul
    co
    #
    @2
    c1
    c2
    cdiv
    co
    #
    cz
    wcel
    #
    wn
    @4
    @5
    wne
    halfnz
    @2
    @7
    @4
    @5
    @2
    @4
    @5
    wceq
    @5
    @3
    cmin
    co
    #
    c1
    wceq
    #
    @7
    @2
    @5
    @3
    c1
    @2
    c2
    cc
    wcel
    #
    cA
    cc
    wcel
    #
    @5
    cc
    wcel
    2cn
    @0
    @11
    @1
    cA
    zcn
    adantr
    #
    c2
    cA
    mulcl
    sylancr
    @2
    @10
    cB
    cc
    wcel
    #
    @3
    cc
    wcel
    2cn
    @1
    @13
    @0
    cB
    zcn
    adantl
    #
    c2
    cB
    mulcl
    sylancr
    @2
    1cnd
    subaddd
    @2
    @8
    c2
    cdiv
    co
    #
    cz
    wcel
    @9
    @7
    @2
    @15
    cA
    cB
    cmin
    co
    #
    cz
    @2
    c2
    @16
    cmul
    co
    #
    c2
    cdiv
    co
    @15
    @16
    @2
    @17
    @8
    c2
    cdiv
    @2
    c2
    cA
    cB
    @10
    @2
    2cn
    a1i
    #
    @12
    @14
    subdid
    oveq1d
    @2
    @16
    c2
    @2
    @16
    cz
    wcel
    @16
    cc
    wcel
    cA
    cB
    zsubcl
    #
    @16
    zcn
    syl
    @18
    c2
    cc0
    wne
    @2
    2ne0
    a1i
    divcan3d
    eqtr3d
    @19
    eqeltrd
    @9
    @15
    @6
    cz
    @8
    c1
    c2
    cdiv
    oveq1
    eleq1d
    syl5ibcom
    sylbird
    necon3bd
    mpi
    necomd
end
