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
include "cc.mm"
include "zcn.mm"
include "mulcom.mm"
include "syl2an.mm"
include "3adant1.mm"
include "breq2d.mm"
include "dvdsmul2.mm"
include "ancoms.mm"
include "3adant2.mm"
include "simp1.mm"
include "zmulcl.mm"
include "dvdsgcd.mm"
include "syl3anc.mm"
include "mpand.mm"
include "sylbid.mm"
include "adantr.mm"
include "cabs.mm"
include "cfv.mm"
include "absmulgcd.mm"
include "3coml.mm"
include "oveq2.mm"
include "mulid1d.mm"
include "sylan9eqr.mm"
include "fveq2d.mm"
include "3ad2antl3.mm"
include "eqtrd.mm"
include "wb.mm"
include "dvdsabsb.mm"
include "bitr4d.mm"
include "sylibd.mm"
include "ex.mm"
include "com23.mm"
include "impd.mm"

theorem coprmdvdsOLD
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
    cK
    cN
    cK
    cmul
    co
    #
    cN
    cM
    cmul
    co
    #
    cgcd
    co
    #
    cdvds
    wbr
    #
    @8
    @3
    @5
    @13
    wi
    @7
    @3
    @5
    cK
    @11
    cdvds
    wbr
    #
    @13
    @3
    @4
    @11
    cK
    cdvds
    @1
    @2
    @4
    @11
    wceq
    #
    @0
    @1
    cM
    cc
    wcel
    cN
    cc
    wcel
    @15
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
    3adant1
    breq2d
    @3
    cK
    @10
    cdvds
    wbr
    #
    @14
    @13
    @0
    @2
    @17
    @1
    @2
    @0
    @17
    cN
    cK
    dvdsmul2
    ancoms
    3adant2
    @3
    @0
    @10
    cz
    wcel
    #
    @11
    cz
    wcel
    #
    @17
    @14
    wa
    @13
    wi
    @0
    @1
    @2
    simp1
    @0
    @2
    @18
    @1
    @2
    @0
    @18
    cN
    cK
    zmulcl
    ancoms
    3adant2
    @1
    @2
    @19
    @0
    @2
    @1
    @19
    cN
    cM
    zmulcl
    ancoms
    3adant1
    cK
    @10
    @11
    dvdsgcd
    syl3anc
    mpand
    sylbid
    adantr
    @9
    @13
    cK
    cN
    cabs
    cfv
    #
    cdvds
    wbr
    #
    @8
    @9
    @12
    @20
    cK
    cdvds
    @9
    @12
    cN
    @6
    cmul
    co
    #
    cabs
    cfv
    #
    @20
    @3
    @12
    @23
    wceq
    #
    @7
    @2
    @0
    @1
    @24
    cN
    cK
    cM
    absmulgcd
    3coml
    adantr
    @2
    @0
    @7
    @23
    @20
    wceq
    @1
    @2
    @7
    wa
    @22
    cN
    cabs
    @7
    @2
    @22
    cN
    c1
    cmul
    co
    cN
    @6
    c1
    cN
    cmul
    oveq2
    @2
    cN
    @16
    mulid1d
    sylan9eqr
    fveq2d
    3ad2antl3
    eqtrd
    breq2d
    @3
    @8
    @21
    wb
    #
    @7
    @0
    @2
    @25
    @1
    cK
    cN
    dvdsabsb
    3adant2
    adantr
    bitr4d
    sylibd
    ex
    com23
    impd
end
