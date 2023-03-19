include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "w3a.mm"
include "cdiv.mm"
include "co.mm"
include "wn.mm"
include "cmul.mm"
include "cle.mm"
include "wb.mm"
include "ltdivmul2.mm"
include "3com12.mm"
include "notbid.mm"
include "simp1.mm"
include "wne.mm"
include "gt0ne0.mm"
include "3adant1.mm"
include "redivcl.mm"
include "syld3an3.mm"
include "3expb.mm"
include "lenltd.mm"
include "remulcl.mm"
include "3adant2.mm"
include "simp2.mm"
include "3adant3r.mm"
include "3bitr4rd.mm"

theorem lemuldiv
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. RR /\ B e. RR /\ ( C e. RR /\ 0 < C ) ) -> ( ( A x. C ) <_ B <-> A <_ ( B / C ) ) )

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
    cC
    cdiv
    co
    #
    cA
    clt
    wbr
    #
    wn
    cB
    cA
    cC
    cmul
    co
    #
    clt
    wbr
    #
    wn
    #
    cA
    @6
    cle
    wbr
    @8
    cB
    cle
    wbr
    #
    @5
    @7
    @9
    @1
    @0
    @4
    @7
    @9
    wb
    cB
    cA
    cC
    ltdivmul2
    3com12
    notbid
    @5
    cA
    @6
    @0
    @1
    @4
    simp1
    @1
    @4
    @6
    cr
    wcel
    #
    @0
    @1
    @2
    @3
    @12
    @1
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
    @1
    cC
    gt0ne0
    3adant1
    cB
    cC
    redivcl
    syld3an3
    3expb
    3adant1
    lenltd
    @0
    @1
    @2
    @11
    @10
    wb
    @3
    @0
    @1
    @2
    w3a
    @8
    cB
    @0
    @2
    @8
    cr
    wcel
    @1
    cA
    cC
    remulcl
    3adant2
    @0
    @1
    @2
    simp2
    lenltd
    3adant3r
    3bitr4rd
end
