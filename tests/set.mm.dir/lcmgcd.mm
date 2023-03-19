include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "wceq.mm"
include "wo.mm"
include "clcm.mm"
include "co.mm"
include "cgcd.mm"
include "cmul.mm"
include "cabs.mm"
include "cfv.mm"
include "gcdcl.mm"
include "nn0cnd.mm"
include "mul02d.mm"
include "0z.mm"
include "lcmcom.mm"
include "mpan2.mm"
include "lcm0val.mm"
include "eqtr3d.mm"
include "adantl.mm"
include "oveq1d.mm"
include "cc.mm"
include "zcn.mm"
include "abs00bd.mm"
include "3eqtr4d.mm"
include "adantr.mm"
include "simpr.mm"
include "fveq2d.mm"
include "mul01d.mm"
include "oveq2d.mm"
include "jaodan.mm"
include "wn.mm"
include "cn.mm"
include "wne.mm"
include "neanior.mm"
include "nnabscl.mm"
include "anim12i.mm"
include "an4s.mm"
include "sylan2br.mm"
include "cdvds.mm"
include "wbr.mm"
include "wi.mm"
include "lcmgcdlem.mm"
include "simpld.mm"
include "syl.mm"
include "lcmabs.mm"
include "gcdabs.mm"
include "oveq12d.mm"
include "absidm.mm"
include "oveqan12d.mm"
include "syl2an.mm"
include "nn0abscl.mm"
include "absmuld.mm"
include "3eqtr3d.mm"
include "pm2.61dan.mm"

theorem lcmgcd
  let cM: class M
  let cN: class N


  assert |- ( ( M e. ZZ /\ N e. ZZ ) -> ( ( M lcm N ) x. ( M gcd N ) ) = ( abs ` ( M x. N ) ) )

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
    cc0
    wceq
    #
    cN
    cc0
    wceq
    #
    wo
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
    cmul
    co
    #
    cM
    cN
    cmul
    co
    #
    cabs
    cfv
    #
    wceq
    #
    @2
    @3
    @11
    @4
    @2
    @3
    wa
    #
    cc0
    cN
    clcm
    co
    #
    @7
    cmul
    co
    #
    cc0
    cN
    cmul
    co
    #
    cabs
    cfv
    #
    @8
    @10
    @2
    @14
    @16
    wceq
    @3
    @2
    cc0
    @7
    cmul
    co
    #
    cc0
    @14
    @16
    @2
    @7
    @2
    @7
    cM
    cN
    gcdcl
    nn0cnd
    mul02d
    #
    @2
    @13
    cc0
    @7
    cmul
    @1
    @13
    cc0
    wceq
    @0
    @1
    cN
    cc0
    clcm
    co
    #
    @13
    cc0
    @1
    cc0
    cz
    wcel
    @19
    @13
    wceq
    0z
    cN
    cc0
    lcmcom
    mpan2
    cN
    lcm0val
    eqtr3d
    adantl
    oveq1d
    @2
    @15
    @2
    cN
    @1
    cN
    cc
    wcel
    #
    @0
    cN
    zcn
    #
    adantl
    #
    mul02d
    abs00bd
    3eqtr4d
    adantr
    @12
    @6
    @13
    @7
    cmul
    @12
    cM
    cc0
    cN
    clcm
    @2
    @3
    simpr
    #
    oveq1d
    oveq1d
    @12
    @9
    @15
    cabs
    @12
    cM
    cc0
    cN
    cmul
    @23
    oveq1d
    fveq2d
    3eqtr4d
    @2
    @4
    wa
    #
    cM
    cc0
    clcm
    co
    #
    @7
    cmul
    co
    #
    cM
    cc0
    cmul
    co
    #
    cabs
    cfv
    #
    @8
    @10
    @2
    @26
    @28
    wceq
    @4
    @2
    @17
    cc0
    @26
    @28
    @18
    @2
    @25
    cc0
    @7
    cmul
    @0
    @25
    cc0
    wceq
    @1
    cM
    lcm0val
    adantr
    oveq1d
    @2
    @27
    @2
    cM
    @0
    cM
    cc
    wcel
    #
    @1
    cM
    zcn
    #
    adantr
    #
    mul01d
    abs00bd
    3eqtr4d
    adantr
    @24
    @6
    @25
    @7
    cmul
    @24
    cN
    cc0
    cM
    clcm
    @2
    @4
    simpr
    #
    oveq2d
    oveq1d
    @24
    @9
    @27
    cabs
    @24
    cN
    cc0
    cM
    cmul
    @32
    oveq2d
    fveq2d
    3eqtr4d
    jaodan
    @2
    @5
    wn
    #
    wa
    #
    cM
    cabs
    cfv
    #
    cN
    cabs
    cfv
    #
    clcm
    co
    #
    @35
    @36
    cgcd
    co
    #
    cmul
    co
    #
    @35
    @36
    cmul
    co
    #
    cabs
    cfv
    #
    @8
    @10
    @34
    @35
    cn
    wcel
    #
    @36
    cn
    wcel
    #
    wa
    #
    @39
    @41
    wceq
    #
    @33
    @2
    cM
    cc0
    wne
    #
    cN
    cc0
    wne
    #
    wa
    @44
    cM
    cc0
    cN
    cc0
    neanior
    @0
    @46
    @1
    @47
    @44
    @0
    @46
    wa
    @42
    @1
    @47
    wa
    @43
    cM
    nnabscl
    cN
    nnabscl
    anim12i
    an4s
    sylan2br
    @44
    @45
    cc0
    cn
    wcel
    @35
    cc0
    cdvds
    wbr
    @36
    cc0
    cdvds
    wbr
    wa
    wa
    @37
    cc0
    cdvds
    wbr
    wi
    cc0
    @35
    @36
    lcmgcdlem
    simpld
    syl
    @2
    @39
    @8
    wceq
    @33
    @2
    @37
    @6
    @38
    @7
    cmul
    cM
    cN
    lcmabs
    cM
    cN
    gcdabs
    oveq12d
    adantr
    @2
    @41
    @10
    wceq
    @33
    @2
    @35
    cabs
    cfv
    #
    @36
    cabs
    cfv
    #
    cmul
    co
    #
    @40
    @41
    @10
    @0
    @29
    @20
    @50
    @40
    wceq
    @1
    @30
    @21
    @29
    @20
    @48
    @35
    @49
    @36
    cmul
    cM
    absidm
    cN
    absidm
    oveqan12d
    syl2an
    @2
    @35
    @36
    @0
    @35
    cc
    wcel
    @1
    @0
    @35
    cM
    nn0abscl
    nn0cnd
    adantr
    @1
    @36
    cc
    wcel
    @0
    @1
    @36
    cN
    nn0abscl
    nn0cnd
    adantl
    absmuld
    @2
    cM
    cN
    @31
    @22
    absmuld
    3eqtr4d
    adantr
    3eqtr3d
    pm2.61dan
end
