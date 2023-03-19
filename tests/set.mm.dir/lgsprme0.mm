include "cz.mm"
include "wcel.mm"
include "cprime.mm"
include "wa.mm"
include "cmo.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "clgs.mm"
include "wne.mm"
include "cgcd.mm"
include "c1.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "wb.mm"
include "prmz.mm"
include "lgsne0.mm"
include "sylan2.mm"
include "coprm.mm"
include "ancoms.mm"
include "anim1i.mm"
include "gcdcom.mm"
include "syl.mm"
include "eqeq1d.mm"
include "bitr2d.mm"
include "cn.mm"
include "prmnn.mm"
include "dvdsval3.mm"
include "sylan.mm"
include "notbid.mm"
include "3bitrd.mm"
include "necon4abid.mm"

theorem lgsprme0
  let cA: class A
  let cP: class P


  assert |- ( ( A e. ZZ /\ P e. Prime ) -> ( ( A /L P ) = 0 <-> ( A mod P ) = 0 ) )

  proof
    cA
    cz
    wcel
    #
    cP
    cprime
    wcel
    #
    wa
    #
    cA
    cP
    cmo
    co
    cc0
    wceq
    #
    cA
    cP
    clgs
    co
    #
    cc0
    @2
    @4
    cc0
    wne
    #
    cA
    cP
    cgcd
    co
    #
    c1
    wceq
    #
    cP
    cA
    cdvds
    wbr
    #
    wn
    #
    @3
    wn
    @1
    @0
    cP
    cz
    wcel
    #
    @5
    @7
    wb
    cP
    prmz
    #
    cA
    cP
    lgsne0
    sylan2
    @2
    @9
    cP
    cA
    cgcd
    co
    #
    c1
    wceq
    #
    @7
    @1
    @0
    @9
    @13
    wb
    cP
    cA
    coprm
    ancoms
    @2
    @12
    @6
    c1
    @2
    @10
    @0
    wa
    #
    @12
    @6
    wceq
    @1
    @0
    @14
    @1
    @10
    @0
    @11
    anim1i
    ancoms
    cP
    cA
    gcdcom
    syl
    eqeq1d
    bitr2d
    @2
    @8
    @3
    @1
    @0
    @8
    @3
    wb
    #
    @1
    cP
    cn
    wcel
    @0
    @15
    cP
    prmnn
    cP
    cA
    dvdsval3
    sylan
    ancoms
    notbid
    3bitrd
    necon4abid
end
