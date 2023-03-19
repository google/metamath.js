include "cz.mm"
include "wcel.mm"
include "w3a.mm"
include "cmul.mm"
include "co.mm"
include "cdvds.mm"
include "wbr.mm"
include "cgcd.mm"
include "c1.mm"
include "wceq.mm"
include "wi.mm"
include "wa.mm"
include "wb.mm"
include "cc.mm"
include "zcn.mm"
include "mulcom.mm"
include "syl2an.mm"
include "breq2d.mm"
include "dvdsmulgcd.mm"
include "ancoms.mm"
include "bitrd.mm"
include "3adant1.mm"
include "adantr.mm"
include "gcdcom.mm"
include "3adant3.mm"
include "eqeq1d.mm"
include "oveq2.mm"
include "syl6bi.mm"
include "imp.mm"
include "mulid1d.mm"
include "3ad2ant3.mm"
include "eqtrd.mm"
include "biimpd.mm"
include "ex.mm"
include "com23.mm"
include "impd.mm"

theorem coprmdvds
  let cK: class K
  let cM: class M
  let cN: class N


  assert |- ( ( K e. ZZ /\ M e. ZZ /\ N e. ZZ ) -> ( ( K || ( M x. N ) /\ ( K gcd M ) = 1 ) -> K || N ) )

  proof
    cK
    cz
    wcel
    #
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    w3a
    #
    cK
    cM
    cN
    cmul
    co
    #
    cdvds
    wbr
    #
    cK
    cM
    cgcd
    co
    #
    c1
    wceq
    #
    cK
    cN
    cdvds
    wbr
    #
    @3
    @7
    @5
    @8
    @3
    @7
    @5
    @8
    wi
    @3
    @7
    wa
    #
    @5
    @8
    @9
    @5
    cK
    cN
    cM
    cK
    cgcd
    co
    #
    cmul
    co
    #
    cdvds
    wbr
    #
    @8
    @3
    @5
    @12
    wb
    #
    @7
    @1
    @2
    @13
    @0
    @1
    @2
    wa
    #
    @5
    cK
    cN
    cM
    cmul
    co
    #
    cdvds
    wbr
    #
    @12
    @14
    @4
    @15
    cK
    cdvds
    @1
    cM
    cc
    wcel
    cN
    cc
    wcel
    @4
    @15
    wceq
    @2
    cM
    zcn
    cN
    zcn
    #
    cM
    cN
    mulcom
    syl2an
    breq2d
    @2
    @1
    @16
    @12
    wb
    cK
    cN
    cM
    dvdsmulgcd
    ancoms
    bitrd
    3adant1
    adantr
    @9
    @11
    cN
    cK
    cdvds
    @9
    @11
    cN
    c1
    cmul
    co
    #
    cN
    @3
    @7
    @11
    @18
    wceq
    #
    @3
    @7
    @10
    c1
    wceq
    @19
    @3
    @6
    @10
    c1
    @0
    @1
    @6
    @10
    wceq
    @2
    cK
    cM
    gcdcom
    3adant3
    eqeq1d
    @10
    c1
    cN
    cmul
    oveq2
    syl6bi
    imp
    @3
    @18
    cN
    wceq
    #
    @7
    @2
    @0
    @20
    @1
    @2
    cN
    @17
    mulid1d
    3ad2ant3
    adantr
    eqtrd
    breq2d
    bitrd
    biimpd
    ex
    com23
    impd
end
