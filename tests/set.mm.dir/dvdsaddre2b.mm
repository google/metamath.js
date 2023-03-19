include "cz.mm"
include "wcel.mm"
include "cr.mm"
include "cdvds.mm"
include "wbr.mm"
include "wa.mm"
include "w3a.mm"
include "caddc.mm"
include "co.mm"
include "wb.mm"
include "wi.mm"
include "dvdsadd2b.mm"
include "a1d.mm"
include "3exp.mm"
include "com24.mm"
include "3imp.mm"
include "com12.mm"
include "wn.mm"
include "dvdszrcl.mm"
include "pm2.24.mm"
include "simpl2im.mm"
include "adantr.mm"
include "cc.mm"
include "zcn.mm"
include "recn.mm"
include "ad2antrl.mm"
include "addcomd.mm"
include "cdif.mm"
include "eldif.mm"
include "nzadd.mm"
include "eldifbd.mm"
include "expcom.mm"
include "syl5bir.mm"
include "imp.mm"
include "eqneltrd.mm"
include "exp32.mm"
include "pm2.21.mm"
include "syl8.mm"
include "a1i.mm"
include "impcom.mm"
include "impbid.mm"
include "ex.mm"
include "pm2.61i.mm"

theorem dvdsaddre2b
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- ( ( A e. ZZ /\ B e. RR /\ ( C e. ZZ /\ A || C ) ) -> ( A || B <-> A || ( C + B ) ) )

  proof
    cB
    cz
    wcel
    #
    cA
    cz
    wcel
    #
    cB
    cr
    wcel
    #
    cC
    cz
    wcel
    #
    cA
    cC
    cdvds
    wbr
    #
    wa
    #
    w3a
    #
    cA
    cB
    cdvds
    wbr
    #
    cA
    cC
    cB
    caddc
    co
    #
    cdvds
    wbr
    #
    wb
    #
    wi
    @6
    @0
    @10
    @1
    @2
    @5
    @0
    @10
    wi
    @1
    @0
    @5
    @2
    @10
    @1
    @0
    @5
    @2
    @10
    wi
    @1
    @0
    @5
    w3a
    @10
    @2
    cA
    cB
    cC
    dvdsadd2b
    a1d
    3exp
    com24
    3imp
    com12
    @0
    wn
    #
    @6
    @10
    @11
    @6
    wa
    #
    @7
    @9
    @11
    @7
    @9
    wi
    @6
    @7
    @11
    @9
    @7
    @1
    @0
    @11
    @9
    wi
    cA
    cB
    dvdszrcl
    @0
    @9
    pm2.24
    simpl2im
    com12
    adantr
    @9
    @12
    @7
    @9
    @1
    @8
    cz
    wcel
    #
    @12
    @7
    wi
    cA
    @8
    dvdszrcl
    @12
    @13
    @7
    @6
    @11
    @13
    @7
    wi
    #
    @1
    @2
    @5
    @11
    @14
    wi
    #
    @2
    @5
    @15
    wi
    wi
    @1
    @5
    @2
    @15
    @3
    @2
    @15
    wi
    @4
    @3
    @2
    @11
    @13
    wn
    #
    @14
    @3
    @2
    @11
    @16
    @3
    @2
    @11
    wa
    #
    wa
    #
    @8
    cB
    cC
    caddc
    co
    #
    cz
    @18
    cC
    cB
    @3
    cC
    cc
    wcel
    @17
    cC
    zcn
    adantr
    @2
    cB
    cc
    wcel
    @3
    @11
    cB
    recn
    ad2antrl
    addcomd
    @3
    @17
    @19
    cz
    wcel
    wn
    #
    @17
    cB
    cr
    cz
    cdif
    wcel
    #
    @3
    @20
    cB
    cr
    cz
    eldif
    @21
    @3
    @20
    @21
    @3
    wa
    @19
    cr
    cz
    cB
    cC
    nzadd
    eldifbd
    expcom
    syl5bir
    imp
    eqneltrd
    exp32
    @13
    @7
    pm2.21
    syl8
    adantr
    com12
    a1i
    3imp
    impcom
    com12
    simpl2im
    com12
    impbid
    ex
    pm2.61i
end
