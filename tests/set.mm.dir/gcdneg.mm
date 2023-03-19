include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cgcd.mm"
include "co.mm"
include "cneg.mm"
include "cc0.mm"
include "wceq.mm"
include "oveq12.mm"
include "adantl.mm"
include "wb.mm"
include "zcn.mm"
include "negeq0d.mm"
include "anbi2d.mm"
include "syl6bi.mm"
include "imp.mm"
include "eqtr4d.mm"
include "wn.mm"
include "cle.mm"
include "wbr.mm"
include "cdvds.mm"
include "gcddvds.mm"
include "gcdcl.mm"
include "nn0zd.mm"
include "dvdsnegb.mm"
include "sylancom.mm"
include "mpbid.mm"
include "wi.mm"
include "notbid.mm"
include "simpl.mm"
include "znegcl.mm"
include "w3a.mm"
include "dvdslegcd.mm"
include "ex.mm"
include "syl3anc.mm"
include "sylbid.mm"
include "com12.mm"
include "mpdi.mm"
include "impcom.mm"
include "sylan2.mm"
include "mpbird.mm"
include "simpr.mm"
include "zred.mm"
include "letri3d.mm"
include "adantr.mm"
include "mpbir2and.mm"
include "pm2.61dan.mm"
include "eqcomd.mm"

theorem gcdneg
  let cM: class M
  let cN: class N


  assert |- ( ( M e. ZZ /\ N e. ZZ ) -> ( M gcd -u N ) = ( M gcd N ) )

  proof
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    wa
    #
    cM
    cN
    cgcd
    co
    #
    cM
    cN
    cneg
    #
    cgcd
    co
    #
    @2
    cM
    cc0
    wceq
    #
    cN
    cc0
    wceq
    #
    wa
    #
    @3
    @5
    wceq
    #
    @2
    @8
    wa
    @3
    cc0
    cc0
    cgcd
    co
    #
    @5
    @8
    @3
    @10
    wceq
    @2
    cM
    cc0
    cN
    cc0
    cgcd
    oveq12
    adantl
    @2
    @8
    @5
    @10
    wceq
    #
    @2
    @8
    @6
    @4
    cc0
    wceq
    #
    wa
    #
    @11
    @1
    @8
    @13
    wb
    @0
    @1
    @7
    @12
    @6
    @1
    cN
    cN
    zcn
    negeq0d
    anbi2d
    adantl
    #
    cM
    cc0
    @4
    cc0
    cgcd
    oveq12
    syl6bi
    imp
    eqtr4d
    @2
    @8
    wn
    #
    wa
    @9
    @3
    @5
    cle
    wbr
    #
    @5
    @3
    cle
    wbr
    #
    @15
    @2
    @16
    @15
    @2
    @3
    cM
    cdvds
    wbr
    #
    @3
    @4
    cdvds
    wbr
    #
    wa
    #
    @16
    @2
    @18
    @3
    cN
    cdvds
    wbr
    #
    wa
    @20
    cM
    cN
    gcddvds
    @2
    @21
    @19
    @18
    @0
    @1
    @3
    cz
    wcel
    #
    @21
    @19
    wb
    @2
    @3
    cM
    cN
    gcdcl
    nn0zd
    #
    @3
    cN
    dvdsnegb
    sylancom
    anbi2d
    mpbid
    @2
    @15
    @20
    @16
    wi
    #
    @2
    @15
    @13
    wn
    #
    @24
    @2
    @8
    @13
    @14
    notbid
    @2
    @22
    @0
    @4
    cz
    wcel
    #
    @25
    @24
    wi
    @23
    @0
    @1
    simpl
    #
    @1
    @26
    @0
    cN
    znegcl
    #
    adantl
    @22
    @0
    @26
    w3a
    @25
    @24
    @3
    cM
    @4
    dvdslegcd
    ex
    syl3anc
    sylbid
    com12
    mpdi
    impcom
    @15
    @2
    @17
    @15
    @2
    @5
    cM
    cdvds
    wbr
    #
    @5
    cN
    cdvds
    wbr
    #
    wa
    #
    @17
    @2
    @31
    @29
    @5
    @4
    cdvds
    wbr
    #
    wa
    #
    @1
    @0
    @26
    @33
    @28
    cM
    @4
    gcddvds
    sylan2
    @2
    @30
    @32
    @29
    @0
    @1
    @5
    cz
    wcel
    #
    @30
    @32
    wb
    @1
    @0
    @26
    @34
    @28
    @0
    @26
    wa
    @5
    cM
    @4
    gcdcl
    nn0zd
    sylan2
    #
    @5
    cN
    dvdsnegb
    sylancom
    anbi2d
    mpbird
    @2
    @15
    @31
    @17
    wi
    #
    @2
    @34
    @0
    @1
    @15
    @36
    wi
    @35
    @27
    @0
    @1
    simpr
    @34
    @0
    @1
    w3a
    @15
    @36
    @5
    cM
    cN
    dvdslegcd
    ex
    syl3anc
    com12
    mpdi
    impcom
    @2
    @9
    @16
    @17
    wa
    wb
    @15
    @2
    @3
    @5
    @2
    @3
    @23
    zred
    @2
    @5
    @35
    zred
    letri3d
    adantr
    mpbir2and
    pm2.61dan
    eqcomd
end
