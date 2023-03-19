include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "w3a.mm"
include "wn.mm"
include "cdiv.mm"
include "co.mm"
include "cle.mm"
include "wb.mm"
include "ltdiv1.mm"
include "3com12.mm"
include "notbid.mm"
include "lenlt.mm"
include "3adant3.mm"
include "wne.mm"
include "gt0ne0.mm"
include "3adant1.mm"
include "redivcl.mm"
include "syld3an3.mm"
include "3expb.mm"
include "3adant2.mm"
include "lenltd.mm"
include "3bitr4d.mm"

theorem lediv1
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. RR /\ B e. RR /\ ( C e. RR /\ 0 < C ) ) -> ( A <_ B <-> ( A / C ) <_ ( B / C ) ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    cC
    cr
    wcel
    #
    cc0
    cC
    clt
    wbr
    #
    wa
    #
    w3a
    #
    cB
    cA
    clt
    wbr
    #
    wn
    #
    cB
    cC
    cdiv
    co
    #
    cA
    cC
    cdiv
    co
    #
    clt
    wbr
    #
    wn
    cA
    cB
    cle
    wbr
    #
    @9
    @8
    cle
    wbr
    @5
    @6
    @10
    @1
    @0
    @4
    @6
    @10
    wb
    cB
    cA
    cC
    ltdiv1
    3com12
    notbid
    @0
    @1
    @11
    @7
    wb
    @4
    cA
    cB
    lenlt
    3adant3
    @5
    @9
    @8
    @0
    @4
    @9
    cr
    wcel
    #
    @1
    @0
    @2
    @3
    @12
    @0
    @2
    @3
    cC
    cc0
    wne
    #
    @12
    @2
    @3
    @13
    @0
    cC
    gt0ne0
    #
    3adant1
    cA
    cC
    redivcl
    syld3an3
    3expb
    3adant2
    @1
    @4
    @8
    cr
    wcel
    #
    @0
    @1
    @2
    @3
    @15
    @1
    @2
    @3
    @13
    @15
    @2
    @3
    @13
    @1
    @14
    3adant1
    cB
    cC
    redivcl
    syld3an3
    3expb
    3adant1
    lenltd
    3bitr4d
end
