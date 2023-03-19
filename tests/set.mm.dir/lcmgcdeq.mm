include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "clcm.mm"
include "co.mm"
include "cgcd.mm"
include "wceq.mm"
include "cabs.mm"
include "cfv.mm"
include "cdvds.mm"
include "wbr.mm"
include "dvdslcm.mm"
include "simpld.mm"
include "adantr.mm"
include "gcddvds.mm"
include "simprd.mm"
include "breq1.mm"
include "syl5ibrcom.mm"
include "imp.mm"
include "wi.mm"
include "lcmcl.mm"
include "nn0zd.mm"
include "dvdstr.mm"
include "syl3an2.mm"
include "3com12.mm"
include "3expb.mm"
include "anidms.mm"
include "mp2and.mm"
include "wb.mm"
include "absdvdsb.mm"
include "zabscl.mm"
include "dvdsabsb.mm"
include "sylan.mm"
include "bitrd.mm"
include "mpbid.mm"
include "3coml.mm"
include "ancoms.mm"
include "cn0.mm"
include "nn0abscl.mm"
include "anim12i.mm"
include "dvdseq.mm"
include "ex.mm"
include "lcmid.mm"
include "syl.mm"
include "gcdid.mm"
include "eqtr4d.mm"
include "oveq2.mm"
include "eqeq12d.mm"
include "syl5ibcom.mm"
include "adantlr.mm"
include "lcmabs.mm"
include "gcdabs.mm"
include "impbida.mm"

theorem lcmgcdeq
  let cM: class M
  let cN: class N


  assert |- ( ( M e. ZZ /\ N e. ZZ ) -> ( ( M lcm N ) = ( M gcd N ) <-> ( abs ` M ) = ( abs ` N ) ) )

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
    clcm
    co
    #
    cM
    cN
    cgcd
    co
    #
    wceq
    #
    cM
    cabs
    cfv
    #
    cN
    cabs
    cfv
    #
    wceq
    #
    @2
    @5
    wa
    #
    @6
    @7
    cdvds
    wbr
    #
    @7
    @6
    cdvds
    wbr
    #
    @8
    @9
    cM
    cN
    cdvds
    wbr
    #
    @10
    @9
    cM
    @3
    cdvds
    wbr
    #
    @3
    cN
    cdvds
    wbr
    #
    @12
    @2
    @13
    @5
    @2
    @13
    cN
    @3
    cdvds
    wbr
    #
    cM
    cN
    dvdslcm
    #
    simpld
    adantr
    @2
    @5
    @14
    @2
    @14
    @5
    @4
    cN
    cdvds
    wbr
    #
    @2
    @4
    cM
    cdvds
    wbr
    #
    @17
    cM
    cN
    gcddvds
    #
    simprd
    @3
    @4
    cN
    cdvds
    breq1
    syl5ibrcom
    imp
    @2
    @13
    @14
    wa
    @12
    wi
    #
    @5
    @2
    @20
    @2
    @0
    @1
    @20
    @0
    @2
    @1
    @20
    @2
    @0
    @3
    cz
    wcel
    #
    @1
    @20
    @2
    @3
    cM
    cN
    lcmcl
    nn0zd
    #
    cM
    @3
    cN
    dvdstr
    syl3an2
    3com12
    3expb
    anidms
    adantr
    mp2and
    @2
    @12
    @10
    wb
    @5
    @2
    @12
    @6
    cN
    cdvds
    wbr
    #
    @10
    cM
    cN
    absdvdsb
    @0
    @6
    cz
    wcel
    #
    @1
    @23
    @10
    wb
    cM
    zabscl
    #
    @6
    cN
    dvdsabsb
    sylan
    bitrd
    adantr
    mpbid
    @9
    cN
    cM
    cdvds
    wbr
    #
    @11
    @9
    @15
    @3
    cM
    cdvds
    wbr
    #
    @26
    @2
    @15
    @5
    @2
    @13
    @15
    @16
    simprd
    adantr
    @2
    @5
    @27
    @2
    @27
    @5
    @18
    @2
    @18
    @17
    @19
    simpld
    @3
    @4
    cM
    cdvds
    breq1
    syl5ibrcom
    imp
    @2
    @15
    @27
    wa
    @26
    wi
    #
    @5
    @2
    @28
    @2
    @0
    @1
    @28
    @1
    @2
    @0
    @28
    @2
    @1
    @21
    @0
    @28
    @22
    cN
    @3
    cM
    dvdstr
    syl3an2
    3coml
    3expb
    anidms
    adantr
    mp2and
    @2
    @26
    @11
    wb
    #
    @5
    @1
    @0
    @29
    @1
    @0
    wa
    @26
    @7
    cM
    cdvds
    wbr
    #
    @11
    cN
    cM
    absdvdsb
    @1
    @7
    cz
    wcel
    @0
    @30
    @11
    wb
    cN
    zabscl
    @7
    cM
    dvdsabsb
    sylan
    bitrd
    ancoms
    adantr
    mpbid
    @2
    @10
    @11
    wa
    #
    @8
    wi
    @5
    @2
    @31
    @8
    @2
    @6
    cn0
    wcel
    #
    @7
    cn0
    wcel
    #
    wa
    @31
    @8
    @0
    @32
    @1
    @33
    cM
    nn0abscl
    cN
    nn0abscl
    anim12i
    @6
    @7
    dvdseq
    sylan
    ex
    adantr
    mp2and
    @2
    @8
    wa
    @6
    @7
    clcm
    co
    #
    @6
    @7
    cgcd
    co
    #
    wceq
    #
    @5
    @0
    @8
    @36
    @1
    @0
    @8
    @36
    @0
    @6
    @6
    clcm
    co
    #
    @6
    @6
    cgcd
    co
    #
    wceq
    @8
    @36
    @0
    @37
    @6
    cabs
    cfv
    #
    @38
    @0
    @24
    @37
    @39
    wceq
    @25
    @6
    lcmid
    syl
    @0
    @24
    @38
    @39
    wceq
    @25
    @6
    gcdid
    syl
    eqtr4d
    @8
    @37
    @34
    @38
    @35
    @6
    @7
    @6
    clcm
    oveq2
    @6
    @7
    @6
    cgcd
    oveq2
    eqeq12d
    syl5ibcom
    imp
    adantlr
    @2
    @36
    @5
    wb
    @8
    @2
    @34
    @3
    @35
    @4
    cM
    cN
    lcmabs
    cM
    cN
    gcdabs
    eqeq12d
    adantr
    mpbid
    impbida
end
