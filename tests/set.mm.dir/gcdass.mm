include "cz.mm"
include "wcel.mm"
include "w3a.mm"
include "cc0.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "crab.mm"
include "cr.mm"
include "clt.mm"
include "csup.mm"
include "cif.mm"
include "cgcd.mm"
include "co.mm"
include "anass.mm"
include "rabbii.mm"
include "supeq1i.mm"
include "ifbieq2i.mm"
include "cn0.mm"
include "gcdcl.mm"
include "3adant3.mm"
include "nn0zd.mm"
include "simp3.mm"
include "gcdval.mm"
include "syl2anc.mm"
include "wb.mm"
include "gcdeq0.mm"
include "anbi1d.mm"
include "bicomd.mm"
include "simpr.mm"
include "simpl1.mm"
include "simpl2.mm"
include "dvdsgcdb.mm"
include "syl3anc.mm"
include "rabbidva.mm"
include "supeq1d.mm"
include "ifbieq2d.mm"
include "eqtr4d.mm"
include "simp1.mm"
include "3adant1.mm"
include "anbi2d.mm"
include "simpl3.mm"
include "3eqtr4a.mm"

theorem gcdass
  let cP: class P
  let cM: class M
  let cN: class N
  let vx: setvar x


  assert |- ( ( N e. ZZ /\ M e. ZZ /\ P e. ZZ ) -> ( ( N gcd M ) gcd P ) = ( N gcd ( M gcd P ) ) )

  proof
    cN
    cz
    wcel
    #
    cM
    cz
    wcel
    #
    cP
    cz
    wcel
    #
    w3a
    #
    cN
    cc0
    wceq
    #
    cM
    cc0
    wceq
    #
    wa
    #
    cP
    cc0
    wceq
    #
    wa
    #
    cc0
    vx
    cv
    #
    cN
    cdvds
    wbr
    #
    @9
    cM
    cdvds
    wbr
    #
    wa
    #
    @9
    cP
    cdvds
    wbr
    #
    wa
    #
    vx
    cz
    crab
    #
    cr
    clt
    csup
    #
    cif
    #
    @4
    @5
    @7
    wa
    #
    wa
    #
    cc0
    @10
    @11
    @13
    wa
    #
    wa
    #
    vx
    cz
    crab
    #
    cr
    clt
    csup
    #
    cif
    #
    cN
    cM
    cgcd
    co
    #
    cP
    cgcd
    co
    #
    cN
    cM
    cP
    cgcd
    co
    #
    cgcd
    co
    #
    @8
    @19
    @16
    @23
    cc0
    @4
    @5
    @7
    anass
    cr
    @15
    @22
    clt
    @14
    @21
    vx
    cz
    @10
    @11
    @13
    anass
    rabbii
    supeq1i
    ifbieq2i
    @3
    @26
    @25
    cc0
    wceq
    #
    @7
    wa
    #
    cc0
    @9
    @25
    cdvds
    wbr
    #
    @13
    wa
    #
    vx
    cz
    crab
    #
    cr
    clt
    csup
    #
    cif
    #
    @17
    @3
    @25
    cz
    wcel
    @2
    @26
    @35
    wceq
    @3
    @25
    @0
    @1
    @25
    cn0
    wcel
    @2
    cN
    cM
    gcdcl
    3adant3
    nn0zd
    @0
    @1
    @2
    simp3
    vx
    @25
    cP
    gcdval
    syl2anc
    @3
    @8
    @30
    @16
    @34
    cc0
    @3
    @30
    @8
    @3
    @29
    @6
    @7
    @0
    @1
    @29
    @6
    wb
    @2
    cN
    cM
    gcdeq0
    3adant3
    anbi1d
    bicomd
    @3
    cr
    @15
    @33
    clt
    @3
    @14
    @32
    vx
    cz
    @3
    @9
    cz
    wcel
    #
    wa
    #
    @12
    @31
    @13
    @37
    @36
    @0
    @1
    @12
    @31
    wb
    @3
    @36
    simpr
    #
    @0
    @1
    @2
    @36
    simpl1
    @0
    @1
    @2
    @36
    simpl2
    #
    @9
    cN
    cM
    dvdsgcdb
    syl3anc
    anbi1d
    rabbidva
    supeq1d
    ifbieq2d
    eqtr4d
    @3
    @28
    @4
    @27
    cc0
    wceq
    #
    wa
    #
    cc0
    @10
    @9
    @27
    cdvds
    wbr
    #
    wa
    #
    vx
    cz
    crab
    #
    cr
    clt
    csup
    #
    cif
    #
    @24
    @3
    @0
    @27
    cz
    wcel
    @28
    @46
    wceq
    @0
    @1
    @2
    simp1
    @3
    @27
    @1
    @2
    @27
    cn0
    wcel
    @0
    cM
    cP
    gcdcl
    3adant1
    nn0zd
    vx
    cN
    @27
    gcdval
    syl2anc
    @3
    @19
    @41
    @23
    @45
    cc0
    @3
    @41
    @19
    @3
    @40
    @18
    @4
    @1
    @2
    @40
    @18
    wb
    @0
    cM
    cP
    gcdeq0
    3adant1
    anbi2d
    bicomd
    @3
    cr
    @22
    @44
    clt
    @3
    @21
    @43
    vx
    cz
    @37
    @20
    @42
    @10
    @37
    @36
    @1
    @2
    @20
    @42
    wb
    @38
    @39
    @0
    @1
    @2
    @36
    simpl3
    @9
    cM
    cP
    dvdsgcdb
    syl3anc
    anbi2d
    rabbidva
    supeq1d
    ifbieq2d
    eqtr4d
    3eqtr4a
end
