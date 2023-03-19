include "cz.mm"
include "wcel.mm"
include "w3a.mm"
include "cgcd.mm"
include "co.mm"
include "c1.mm"
include "wceq.mm"
include "wa.mm"
include "cdvds.mm"
include "wbr.mm"
include "cmul.mm"
include "cv.mm"
include "wrex.mm"
include "wi.mm"
include "wb.mm"
include "divides.mm"
include "3adant1.mm"
include "adantr.mm"
include "simprr.mm"
include "simpl2.mm"
include "cc.mm"
include "zcn.mm"
include "mulcom.mm"
include "syl2an.mm"
include "syl2anc.mm"
include "breq2d.mm"
include "simprl.mm"
include "simpl1.mm"
include "coprmdvds.mm"
include "syl3anc.mm"
include "mpan2d.mm"
include "sylbid.mm"
include "dvdsmulc.mm"
include "syld.mm"
include "breq2.mm"
include "imbi12d.mm"
include "syl5ibcom.mm"
include "anassrs.mm"
include "rexlimdva.mm"
include "com23.mm"
include "impd.mm"

theorem coprmdvds2
  let cK: class K
  let cM: class M
  let cN: class N
  let vx: setvar x


  assert |- ( ( ( M e. ZZ /\ N e. ZZ /\ K e. ZZ ) /\ ( M gcd N ) = 1 ) -> ( ( M || K /\ N || K ) -> ( M x. N ) || K ) )

  proof
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    cK
    cz
    wcel
    #
    w3a
    #
    cM
    cN
    cgcd
    co
    c1
    wceq
    #
    wa
    #
    cM
    cK
    cdvds
    wbr
    #
    cN
    cK
    cdvds
    wbr
    #
    cM
    cN
    cmul
    co
    #
    cK
    cdvds
    wbr
    #
    @5
    @7
    @6
    @9
    @5
    @7
    vx
    cv
    #
    cN
    cmul
    co
    #
    cK
    wceq
    #
    vx
    cz
    wrex
    #
    @6
    @9
    wi
    #
    @3
    @7
    @13
    wb
    #
    @4
    @1
    @2
    @15
    @0
    vx
    cN
    cK
    divides
    3adant1
    adantr
    @5
    @12
    @14
    vx
    cz
    @3
    @4
    @10
    cz
    wcel
    #
    @12
    @14
    wi
    @3
    @4
    @16
    wa
    #
    wa
    #
    cM
    @11
    cdvds
    wbr
    #
    @8
    @11
    cdvds
    wbr
    #
    wi
    @12
    @14
    @18
    @19
    cM
    @10
    cdvds
    wbr
    #
    @20
    @18
    @19
    cM
    cN
    @10
    cmul
    co
    #
    cdvds
    wbr
    #
    @21
    @18
    @11
    @22
    cM
    cdvds
    @18
    @16
    @1
    @11
    @22
    wceq
    #
    @3
    @4
    @16
    simprr
    #
    @0
    @1
    @2
    @17
    simpl2
    #
    @16
    @10
    cc
    wcel
    cN
    cc
    wcel
    @24
    @1
    @10
    zcn
    cN
    zcn
    @10
    cN
    mulcom
    syl2an
    syl2anc
    breq2d
    @18
    @23
    @4
    @21
    @3
    @4
    @16
    simprl
    @18
    @0
    @1
    @16
    @23
    @4
    wa
    @21
    wi
    @0
    @1
    @2
    @17
    simpl1
    #
    @26
    @25
    cM
    cN
    @10
    coprmdvds
    syl3anc
    mpan2d
    sylbid
    @18
    @0
    @16
    @1
    @21
    @20
    wi
    @27
    @25
    @26
    cN
    cM
    @10
    dvdsmulc
    syl3anc
    syld
    @12
    @19
    @6
    @20
    @9
    @11
    cK
    cM
    cdvds
    breq2
    @11
    cK
    @8
    cdvds
    breq2
    imbi12d
    syl5ibcom
    anassrs
    rexlimdva
    sylbid
    com23
    impd
end
