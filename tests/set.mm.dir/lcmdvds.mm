include "cz.mm"
include "wcel.mm"
include "w3a.mm"
include "cc0.mm"
include "wceq.mm"
include "cdvds.mm"
include "wbr.mm"
include "wa.mm"
include "clcm.mm"
include "co.mm"
include "wi.mm"
include "id.mm"
include "wb.mm"
include "breq1.mm"
include "adantl.mm"
include "oveq1.mm"
include "0z.mm"
include "lcmcom.mm"
include "mpan.mm"
include "lcm0val.mm"
include "eqtrd.mm"
include "sylan9eqr.mm"
include "breq1d.mm"
include "imbi12d.mm"
include "mpbiri.mm"
include "3ad2antl3.mm"
include "adantrd.mm"
include "ex.mm"
include "oveq2.mm"
include "3ad2antl2.mm"
include "adantld.mm"
include "wo.mm"
include "wn.mm"
include "wne.mm"
include "neanior.mm"
include "lcmcl.mm"
include "nn0zd.mm"
include "dvds0.mm"
include "syl.mm"
include "a1d.mm"
include "adantr.mm"
include "breq2.mm"
include "anbi12d.mm"
include "mpbird.mm"
include "adantrl.mm"
include "adantllr.mm"
include "adantlrr.mm"
include "anassrs.mm"
include "cabs.mm"
include "cfv.mm"
include "cn.mm"
include "nnabscl.mm"
include "cgcd.mm"
include "cmul.mm"
include "lcmgcdlem.mm"
include "simprd.mm"
include "sylani.mm"
include "syl2an.mm"
include "expdimp.mm"
include "dvdsabsb.mm"
include "zabscl.mm"
include "absdvdsb.mm"
include "sylan2.mm"
include "bitrd.mm"
include "adantlr.mm"
include "adantll.mm"
include "bicomd.mm"
include "lcmabs.mm"
include "sylan.mm"
include "bitr4d.mm"
include "adantrr.mm"
include "mpbid.mm"
include "pm2.61dane.mm"
include "an4s.mm"
include "sylan2br.mm"
include "impancom.mm"
include "3impa.mm"
include "3comr.mm"
include "ecase3d.mm"

theorem lcmdvds
  let cK: class K
  let cM: class M
  let cN: class N


  assert |- ( ( K e. ZZ /\ M e. ZZ /\ N e. ZZ ) -> ( ( M || K /\ N || K ) -> ( M lcm N ) || K ) )

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
    cM
    cc0
    wceq
    #
    cN
    cc0
    wceq
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
    wa
    #
    cM
    cN
    clcm
    co
    #
    cK
    cdvds
    wbr
    #
    wi
    #
    @3
    @4
    @11
    @3
    @4
    wa
    @6
    @10
    @7
    @2
    @0
    @4
    @6
    @10
    wi
    #
    @1
    @2
    @4
    wa
    #
    @12
    cc0
    cK
    cdvds
    wbr
    #
    @14
    wi
    #
    @14
    id
    #
    @13
    @6
    @14
    @10
    @14
    @4
    @6
    @14
    wb
    @2
    cM
    cc0
    cK
    cdvds
    breq1
    adantl
    @13
    @9
    cc0
    cK
    cdvds
    @4
    @2
    @9
    cc0
    cN
    clcm
    co
    #
    cc0
    cM
    cc0
    cN
    clcm
    oveq1
    @2
    @17
    cN
    cc0
    clcm
    co
    #
    cc0
    cc0
    cz
    wcel
    @2
    @17
    @18
    wceq
    0z
    cc0
    cN
    lcmcom
    mpan
    cN
    lcm0val
    eqtrd
    sylan9eqr
    breq1d
    imbi12d
    mpbiri
    3ad2antl3
    adantrd
    ex
    @3
    @5
    @11
    @3
    @5
    wa
    @7
    @10
    @6
    @1
    @0
    @5
    @7
    @10
    wi
    #
    @2
    @1
    @5
    wa
    #
    @19
    @15
    @16
    @20
    @7
    @14
    @10
    @14
    @5
    @7
    @14
    wb
    @1
    cN
    cc0
    cK
    cdvds
    breq1
    adantl
    @20
    @9
    cc0
    cK
    cdvds
    @5
    @1
    @9
    cM
    cc0
    clcm
    co
    cc0
    cN
    cc0
    cM
    clcm
    oveq2
    cM
    lcm0val
    sylan9eqr
    breq1d
    imbi12d
    mpbiri
    3ad2antl2
    adantld
    ex
    @1
    @2
    @0
    @4
    @5
    wo
    wn
    #
    @11
    wi
    #
    @1
    @2
    @0
    @22
    @1
    @2
    wa
    #
    @21
    @0
    @11
    @21
    @23
    cM
    cc0
    wne
    #
    cN
    cc0
    wne
    #
    wa
    @0
    @11
    wi
    #
    cM
    cc0
    cN
    cc0
    neanior
    @1
    @24
    @2
    @25
    @26
    @1
    @24
    wa
    #
    @2
    @25
    wa
    #
    wa
    #
    @0
    @11
    @29
    @0
    wa
    @11
    cK
    cc0
    @29
    @0
    cK
    cc0
    wceq
    #
    @11
    @27
    @2
    @0
    @30
    wa
    #
    @11
    @25
    @1
    @2
    @31
    @11
    @24
    @23
    @30
    @11
    @0
    @23
    @30
    wa
    @11
    cM
    cc0
    cdvds
    wbr
    #
    cN
    cc0
    cdvds
    wbr
    #
    wa
    #
    @9
    cc0
    cdvds
    wbr
    #
    wi
    #
    @23
    @36
    @30
    @23
    @35
    @34
    @23
    @9
    cz
    wcel
    #
    @35
    @23
    @9
    cM
    cN
    lcmcl
    nn0zd
    #
    @9
    dvds0
    syl
    a1d
    adantr
    @30
    @11
    @36
    wb
    @23
    @30
    @8
    @34
    @10
    @35
    @30
    @6
    @32
    @7
    @33
    cK
    cc0
    cM
    cdvds
    breq2
    cK
    cc0
    cN
    cdvds
    breq2
    anbi12d
    cK
    cc0
    @9
    cdvds
    breq2
    imbi12d
    adantl
    mpbird
    adantrl
    adantllr
    adantlrr
    anassrs
    @29
    @0
    cK
    cc0
    wne
    #
    @11
    @29
    @0
    @39
    wa
    #
    wa
    cM
    cabs
    cfv
    #
    cK
    cabs
    cfv
    #
    cdvds
    wbr
    #
    cN
    cabs
    cfv
    #
    @42
    cdvds
    wbr
    #
    wa
    #
    @41
    @44
    clcm
    co
    #
    @42
    cdvds
    wbr
    #
    wi
    #
    @11
    @29
    @40
    @46
    @48
    @27
    @41
    cn
    wcel
    #
    @44
    cn
    wcel
    #
    @40
    @46
    wa
    @48
    wi
    @28
    cM
    nnabscl
    cN
    nnabscl
    @40
    @50
    @51
    wa
    #
    @42
    cn
    wcel
    #
    @46
    @48
    cK
    nnabscl
    @52
    @47
    @41
    @44
    cgcd
    co
    cmul
    co
    @41
    @44
    cmul
    co
    cabs
    cfv
    wceq
    @53
    @46
    wa
    @48
    wi
    @42
    @41
    @44
    lcmgcdlem
    simprd
    sylani
    syl2an
    expdimp
    @27
    @2
    @40
    @49
    @11
    wb
    #
    @25
    @1
    @2
    @40
    @54
    @24
    @23
    @0
    @54
    @39
    @23
    @0
    wa
    #
    @46
    @8
    @48
    @10
    @55
    @8
    @46
    @55
    @6
    @43
    @7
    @45
    @1
    @0
    @6
    @43
    wb
    @2
    @1
    @0
    wa
    @6
    cM
    @42
    cdvds
    wbr
    #
    @43
    cM
    cK
    dvdsabsb
    @0
    @1
    @42
    cz
    wcel
    #
    @56
    @43
    wb
    cK
    zabscl
    #
    cM
    @42
    absdvdsb
    sylan2
    bitrd
    adantlr
    @2
    @0
    @7
    @45
    wb
    @1
    @2
    @0
    wa
    @7
    cN
    @42
    cdvds
    wbr
    #
    @45
    cN
    cK
    dvdsabsb
    @0
    @2
    @57
    @59
    @45
    wb
    @58
    cN
    @42
    absdvdsb
    sylan2
    bitrd
    adantll
    anbi12d
    bicomd
    @55
    @48
    @9
    @42
    cdvds
    wbr
    #
    @10
    @23
    @48
    @60
    wb
    @0
    @23
    @47
    @9
    @42
    cdvds
    cM
    cN
    lcmabs
    breq1d
    adantr
    @23
    @37
    @0
    @10
    @60
    wb
    @38
    @9
    cK
    dvdsabsb
    sylan
    bitr4d
    imbi12d
    adantrr
    adantllr
    adantlrr
    mpbid
    anassrs
    pm2.61dane
    ex
    an4s
    sylan2br
    impancom
    3impa
    3comr
    ecase3d
end
