include "cz.mm"
include "wcel.mm"
include "w3a.mm"
include "cc0.mm"
include "wceq.mm"
include "wo.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "wa.mm"
include "cn.mm"
include "crab.mm"
include "cr.mm"
include "clt.mm"
include "cinf.mm"
include "cif.mm"
include "clcm.mm"
include "co.mm"
include "orass.mm"
include "anass.mm"
include "rabbii.mm"
include "infeq1i.mm"
include "ifbieq2i.mm"
include "cn0.mm"
include "lcmcl.mm"
include "3adant3.mm"
include "nn0zd.mm"
include "simp3.mm"
include "lcmval.mm"
include "syl2anc.mm"
include "wb.mm"
include "lcmeq0.mm"
include "orbi1d.mm"
include "bicomd.mm"
include "nnz.mm"
include "adantl.mm"
include "simp1.mm"
include "adantr.mm"
include "simpl2.mm"
include "lcmdvdsb.mm"
include "syl3anc.mm"
include "anbi1d.mm"
include "rabbidva.mm"
include "infeq1d.mm"
include "ifbieq2d.mm"
include "eqtr4d.mm"
include "3adant1.mm"
include "orbi2d.mm"
include "anbi2d.mm"
include "3eqtr4a.mm"

theorem lcmass
  let cP: class P
  let cM: class M
  let cN: class N
  let vx: setvar x


  assert |- ( ( N e. ZZ /\ M e. ZZ /\ P e. ZZ ) -> ( ( N lcm M ) lcm P ) = ( N lcm ( M lcm P ) ) )

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
    wo
    #
    cP
    cc0
    wceq
    #
    wo
    #
    cc0
    cN
    vx
    cv
    #
    cdvds
    wbr
    #
    cM
    @9
    cdvds
    wbr
    #
    wa
    #
    cP
    @9
    cdvds
    wbr
    #
    wa
    #
    vx
    cn
    crab
    #
    cr
    clt
    cinf
    #
    cif
    #
    @4
    @5
    @7
    wo
    #
    wo
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
    cn
    crab
    #
    cr
    clt
    cinf
    #
    cif
    #
    cN
    cM
    clcm
    co
    #
    cP
    clcm
    co
    #
    cN
    cM
    cP
    clcm
    co
    #
    clcm
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
    orass
    cr
    @15
    @22
    clt
    @14
    @21
    vx
    cn
    @10
    @11
    @13
    anass
    rabbii
    infeq1i
    ifbieq2i
    @3
    @26
    @25
    cc0
    wceq
    #
    @7
    wo
    #
    cc0
    @25
    @9
    cdvds
    wbr
    #
    @13
    wa
    #
    vx
    cn
    crab
    #
    cr
    clt
    cinf
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
    lcmcl
    3adant3
    nn0zd
    @0
    @1
    @2
    simp3
    #
    vx
    @25
    cP
    lcmval
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
    lcmeq0
    3adant3
    orbi1d
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
    cn
    @3
    @9
    cn
    wcel
    #
    wa
    #
    @12
    @31
    @13
    @38
    @9
    cz
    wcel
    #
    @0
    @1
    @12
    @31
    wb
    @37
    @39
    @3
    @9
    nnz
    adantl
    #
    @3
    @0
    @37
    @0
    @1
    @2
    simp1
    #
    adantr
    @0
    @1
    @2
    @37
    simpl2
    #
    @9
    cN
    cM
    lcmdvdsb
    syl3anc
    anbi1d
    rabbidva
    infeq1d
    ifbieq2d
    eqtr4d
    @3
    @28
    @4
    @27
    cc0
    wceq
    #
    wo
    #
    cc0
    @10
    @27
    @9
    cdvds
    wbr
    #
    wa
    #
    vx
    cn
    crab
    #
    cr
    clt
    cinf
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
    @49
    wceq
    @41
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
    lcmcl
    3adant1
    nn0zd
    vx
    cN
    @27
    lcmval
    syl2anc
    @3
    @19
    @44
    @23
    @48
    cc0
    @3
    @44
    @19
    @3
    @43
    @18
    @4
    @1
    @2
    @43
    @18
    wb
    @0
    cM
    cP
    lcmeq0
    3adant1
    orbi2d
    bicomd
    @3
    cr
    @22
    @47
    clt
    @3
    @21
    @46
    vx
    cn
    @38
    @20
    @45
    @10
    @38
    @39
    @1
    @2
    @20
    @45
    wb
    @40
    @42
    @3
    @2
    @37
    @36
    adantr
    @9
    cM
    cP
    lcmdvdsb
    syl3anc
    anbi2d
    rabbidva
    infeq1d
    ifbieq2d
    eqtr4d
    3eqtr4a
end
