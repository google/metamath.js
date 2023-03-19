include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "clcm.mm"
include "co.mm"
include "cneg.mm"
include "cc0.mm"
include "wceq.mm"
include "wo.mm"
include "lcm0val.mm"
include "znegcl.mm"
include "syl.mm"
include "eqtr4d.mm"
include "ad2antlr.mm"
include "wb.mm"
include "oveq2.mm"
include "eqeq12d.mm"
include "adantl.mm"
include "mpbird.mm"
include "lcmcom.mm"
include "sylan2.mm"
include "adantr.mm"
include "neg0.mm"
include "oveq2i.mm"
include "eqcomi.mm"
include "negeq.mm"
include "oveq2d.mm"
include "3eqtr4a.mm"
include "jaodan.mm"
include "wn.mm"
include "cle.mm"
include "wbr.mm"
include "cdvds.mm"
include "dvdslcm.mm"
include "simpr.mm"
include "cn0.mm"
include "lcmcl.mm"
include "nn0zd.mm"
include "negdvdsb.mm"
include "syl2anc.mm"
include "anbi2d.mm"
include "cn.mm"
include "w3a.mm"
include "wi.mm"
include "zcn.mm"
include "negeq0d.mm"
include "orbi2d.mm"
include "notbid.mm"
include "biimpa.mm"
include "adantll.mm"
include "lcmn0cl.mm"
include "sylanl2.mm"
include "syldan.mm"
include "simpl.mm"
include "3anass.mm"
include "sylanbrc.mm"
include "lcmledvds.mm"
include "mpd.mm"
include "simplr.mm"
include "nnzd.mm"
include "ex.mm"
include "syl3an3.mm"
include "3expib.mm"
include "syl3c.mm"
include "sylbid.mm"
include "nn0red.mm"
include "cr.mm"
include "letri3d.mm"
include "mpbir2and.mm"
include "pm2.61dan.mm"
include "eqcomd.mm"

theorem lcmneg
  let cM: class M
  let cN: class N


  assert |- ( ( M e. ZZ /\ N e. ZZ ) -> ( M lcm -u N ) = ( M lcm N ) )

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
    cneg
    #
    clcm
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
    wo
    #
    @3
    @5
    wceq
    #
    @2
    @6
    @9
    @7
    @2
    @6
    wa
    #
    @9
    cN
    cM
    clcm
    co
    #
    @4
    cM
    clcm
    co
    #
    wceq
    #
    @10
    @13
    cN
    cc0
    clcm
    co
    #
    @4
    cc0
    clcm
    co
    #
    wceq
    #
    @1
    @16
    @0
    @6
    @1
    @14
    cc0
    @15
    cN
    lcm0val
    @1
    @4
    cz
    wcel
    #
    @15
    cc0
    wceq
    cN
    znegcl
    #
    @4
    lcm0val
    syl
    eqtr4d
    ad2antlr
    @6
    @13
    @16
    wb
    @2
    @6
    @11
    @14
    @12
    @15
    cM
    cc0
    cN
    clcm
    oveq2
    cM
    cc0
    @4
    clcm
    oveq2
    eqeq12d
    adantl
    mpbird
    @2
    @9
    @13
    wb
    @6
    @2
    @3
    @11
    @5
    @12
    cM
    cN
    lcmcom
    @1
    @0
    @17
    @5
    @12
    wceq
    @18
    cM
    @4
    lcmcom
    sylan2
    eqeq12d
    adantr
    mpbird
    @7
    @9
    @2
    @7
    cM
    cc0
    clcm
    co
    #
    cM
    cc0
    cneg
    #
    clcm
    co
    #
    @3
    @5
    @21
    @19
    @20
    cc0
    cM
    clcm
    neg0
    oveq2i
    eqcomi
    cN
    cc0
    cM
    clcm
    oveq2
    @7
    @4
    @20
    cM
    clcm
    cN
    cc0
    negeq
    oveq2d
    3eqtr4a
    adantl
    jaodan
    @2
    @8
    wn
    #
    wa
    #
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
    @23
    cM
    @5
    cdvds
    wbr
    #
    cN
    @5
    cdvds
    wbr
    #
    wa
    #
    @24
    @2
    @28
    @22
    @2
    @28
    @26
    @4
    @5
    cdvds
    wbr
    #
    wa
    #
    @1
    @0
    @17
    @30
    @18
    cM
    @4
    dvdslcm
    sylan2
    @2
    @27
    @29
    @26
    @2
    @1
    @5
    cz
    wcel
    @27
    @29
    wb
    @0
    @1
    simpr
    @2
    @5
    @1
    @0
    @17
    @5
    cn0
    wcel
    @18
    cM
    @4
    lcmcl
    #
    sylan2
    nn0zd
    cN
    @5
    negdvdsb
    syl2anc
    anbi2d
    mpbird
    adantr
    @23
    @5
    cn
    wcel
    #
    @0
    @1
    w3a
    #
    @22
    @28
    @24
    wi
    @23
    @32
    @2
    @33
    @2
    @22
    @6
    @4
    cc0
    wceq
    #
    wo
    #
    wn
    #
    @32
    @1
    @22
    @36
    @0
    @1
    @22
    @36
    @1
    @8
    @35
    @1
    @7
    @34
    @6
    @1
    cN
    cN
    zcn
    negeq0d
    orbi2d
    notbid
    biimpa
    adantll
    #
    @1
    @0
    @17
    @36
    @32
    @18
    cM
    @4
    lcmn0cl
    sylanl2
    syldan
    @2
    @22
    simpl
    #
    @32
    @0
    @1
    3anass
    sylanbrc
    @2
    @22
    simpr
    @5
    cM
    cN
    lcmledvds
    syl2anc
    mpd
    @23
    cM
    @3
    cdvds
    wbr
    #
    cN
    @3
    cdvds
    wbr
    #
    wa
    #
    @25
    @2
    @41
    @22
    cM
    cN
    dvdslcm
    adantr
    @23
    @41
    @39
    @4
    @3
    cdvds
    wbr
    #
    wa
    #
    @25
    @23
    @40
    @42
    @39
    @23
    @1
    @3
    cz
    wcel
    @40
    @42
    wb
    @0
    @1
    @22
    simplr
    @23
    @3
    cM
    cN
    lcmn0cl
    #
    nnzd
    cN
    @3
    negdvdsb
    syl2anc
    anbi2d
    @23
    @3
    cn
    wcel
    #
    @2
    @36
    @43
    @25
    wi
    #
    @44
    @38
    @37
    @45
    @0
    @1
    @36
    @46
    wi
    #
    @1
    @45
    @0
    @17
    @47
    @18
    @45
    @0
    @17
    w3a
    @36
    @46
    @3
    cM
    @4
    lcmledvds
    ex
    syl3an3
    3expib
    syl3c
    sylbid
    mpd
    @2
    @9
    @24
    @25
    wa
    wb
    @22
    @2
    @3
    @5
    @2
    @3
    cM
    cN
    lcmcl
    nn0red
    @1
    @0
    @17
    @5
    cr
    wcel
    @18
    @0
    @17
    wa
    @5
    @31
    nn0red
    sylan2
    letri3d
    adantr
    mpbir2and
    pm2.61dan
    eqcomd
end
