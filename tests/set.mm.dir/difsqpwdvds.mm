include "cn0.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "cprime.mm"
include "wa.mm"
include "cexp.mm"
include "c2.mm"
include "cmin.mm"
include "wceq.mm"
include "cmul.mm"
include "cdvds.mm"
include "cc.mm"
include "nn0cn.mm"
include "anim12i.mm"
include "3adant3.mm"
include "subsq.mm"
include "syl.mm"
include "adantr.mm"
include "eqeq2d.mm"
include "cv.mm"
include "cn.mm"
include "wrex.mm"
include "cuz.mm"
include "cfv.mm"
include "simprl.mm"
include "cz.mm"
include "nn0z.mm"
include "zaddcl.mm"
include "cr.mm"
include "nn0re.mm"
include "adantl.mm"
include "1red.mm"
include "ltaddsub2d.mm"
include "wi.mm"
include "simpr.mm"
include "3jca.mm"
include "difgtsumgt.mm"
include "sylbid.mm"
include "3impia.mm"
include "eluz2b1.mm"
include "sylanbrc.mm"
include "simprr.mm"
include "zsubcl.mm"
include "jca.mm"
include "dvdsmul1.mm"
include "ad2antrr.mm"
include "wb.mm"
include "breq2.mm"
include "mpbird.mm"
include "dvdsprmpweqnn.mm"
include "sylc.mm"
include "prmz.mm"
include "iddvdsexp.mm"
include "sylan.mm"
include "syl5ibrcom.mm"
include "rexlimdva.mm"
include "biimp3a.mm"
include "dvdsmul2.mm"
include "anim12ci.mm"
include "3anass.mm"
include "sylibr.mm"
include "dvds2sub.mm"
include "3ad2ant1.mm"
include "3ad2ant2.mm"
include "pnncand.mm"
include "2timesd.mm"
include "eqcomd.mm"
include "eqtrd.mm"
include "breq2d.mm"
include "biimpd.mm"
include "syld.mm"
include "expcomd.mm"
include "mpd.mm"
include "ex.mm"

theorem difsqpwdvds
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vm: setvar m
  let vn: setvar n


  assert |- ( ( ( A e. NN0 /\ B e. NN0 /\ ( B + 1 ) < A ) /\ ( C e. Prime /\ D e. NN0 ) ) -> ( ( C ^ D ) = ( ( A ^ 2 ) - ( B ^ 2 ) ) -> C || ( 2 x. B ) ) )

  proof
    cA
    cn0
    wcel
    #
    cB
    cn0
    wcel
    #
    cB
    c1
    caddc
    co
    cA
    clt
    wbr
    #
    w3a
    #
    cC
    cprime
    wcel
    #
    cD
    cn0
    wcel
    #
    wa
    #
    wa
    #
    cC
    cD
    cexp
    co
    #
    cA
    c2
    cexp
    co
    cB
    c2
    cexp
    co
    cmin
    co
    #
    wceq
    @8
    cA
    cB
    caddc
    co
    #
    cA
    cB
    cmin
    co
    #
    cmul
    co
    #
    wceq
    #
    cC
    c2
    cB
    cmul
    co
    #
    cdvds
    wbr
    #
    @7
    @9
    @12
    @8
    @3
    @9
    @12
    wceq
    #
    @6
    @3
    cA
    cc
    wcel
    #
    cB
    cc
    wcel
    #
    wa
    #
    @16
    @0
    @1
    @19
    @2
    @0
    @17
    @1
    @18
    cA
    nn0cn
    #
    cB
    nn0cn
    #
    anim12i
    3adant3
    cA
    cB
    subsq
    syl
    adantr
    eqeq2d
    @7
    @13
    @15
    @7
    @13
    wa
    #
    @10
    cC
    vm
    cv
    #
    cexp
    co
    #
    wceq
    #
    vm
    cn
    wrex
    #
    @15
    @22
    @4
    @10
    c2
    cuz
    cfv
    #
    wcel
    #
    @5
    w3a
    #
    @10
    @8
    cdvds
    wbr
    #
    @26
    @7
    @29
    @13
    @7
    @4
    @28
    @5
    @3
    @4
    @5
    simprl
    #
    @3
    @28
    @6
    @3
    @10
    cz
    wcel
    #
    c1
    @10
    clt
    wbr
    #
    @28
    @0
    @1
    @32
    @2
    @0
    @1
    wa
    #
    cA
    cz
    wcel
    #
    cB
    cz
    wcel
    #
    wa
    #
    @32
    @0
    @35
    @1
    @36
    cA
    nn0z
    cB
    nn0z
    anim12i
    #
    cA
    cB
    zaddcl
    #
    syl
    3adant3
    @0
    @1
    @2
    @33
    @34
    @2
    c1
    @11
    clt
    wbr
    #
    @33
    @34
    cB
    c1
    cA
    @1
    cB
    cr
    wcel
    @0
    cB
    nn0re
    adantl
    @34
    1red
    #
    @0
    cA
    cr
    wcel
    #
    @1
    cA
    nn0re
    adantr
    #
    ltaddsub2d
    #
    @34
    @42
    @1
    c1
    cr
    wcel
    #
    w3a
    @40
    @33
    wi
    @34
    @42
    @1
    @45
    @43
    @0
    @1
    simpr
    @41
    3jca
    cA
    cB
    c1
    difgtsumgt
    syl
    sylbid
    3impia
    @10
    eluz2b1
    sylanbrc
    adantr
    @3
    @4
    @5
    simprr
    #
    3jca
    adantr
    @22
    @30
    @10
    @12
    cdvds
    wbr
    #
    @3
    @47
    @6
    @13
    @3
    @32
    @11
    cz
    wcel
    #
    wa
    #
    @47
    @0
    @1
    @49
    @2
    @34
    @37
    @49
    @38
    @37
    @32
    @48
    @39
    cA
    cB
    zsubcl
    #
    jca
    syl
    3adant3
    #
    @10
    @11
    dvdsmul1
    syl
    ad2antrr
    @13
    @30
    @47
    wb
    @7
    @8
    @12
    @10
    cdvds
    breq2
    adantl
    mpbird
    @10
    cC
    vm
    cD
    dvdsprmpweqnn
    sylc
    @22
    @26
    cC
    @10
    cdvds
    wbr
    #
    @15
    @7
    @26
    @52
    wi
    #
    @13
    @6
    @53
    @3
    @4
    @53
    @5
    @4
    @25
    @52
    vm
    cn
    @4
    @23
    cn
    wcel
    #
    wa
    @52
    @25
    cC
    @24
    cdvds
    wbr
    #
    @4
    cC
    cz
    wcel
    #
    @54
    @55
    cC
    prmz
    #
    cC
    @23
    iddvdsexp
    sylan
    @10
    @24
    cC
    cdvds
    breq2
    syl5ibrcom
    rexlimdva
    adantr
    adantl
    adantr
    @22
    @11
    cC
    vn
    cv
    #
    cexp
    co
    #
    wceq
    #
    vn
    cn
    wrex
    #
    @52
    @15
    wi
    #
    @22
    @4
    @11
    @27
    wcel
    #
    @5
    w3a
    #
    @11
    @8
    cdvds
    wbr
    #
    @61
    @7
    @64
    @13
    @7
    @4
    @63
    @5
    @31
    @3
    @63
    @6
    @3
    @48
    @40
    @63
    @0
    @1
    @48
    @2
    @34
    @37
    @48
    @38
    @50
    syl
    3adant3
    @0
    @1
    @2
    @40
    @44
    biimp3a
    @11
    eluz2b1
    sylanbrc
    adantr
    @46
    3jca
    adantr
    @22
    @65
    @11
    @12
    cdvds
    wbr
    #
    @3
    @66
    @6
    @13
    @3
    @49
    @66
    @51
    @10
    @11
    dvdsmul2
    syl
    ad2antrr
    @13
    @65
    @66
    wb
    @7
    @8
    @12
    @11
    cdvds
    breq2
    adantl
    mpbird
    @11
    cC
    vn
    cD
    dvdsprmpweqnn
    sylc
    @22
    @61
    cC
    @11
    cdvds
    wbr
    #
    @62
    @7
    @61
    @67
    wi
    #
    @13
    @6
    @68
    @3
    @4
    @68
    @5
    @4
    @60
    @67
    vn
    cn
    @4
    @58
    cn
    wcel
    #
    wa
    @67
    @60
    cC
    @59
    cdvds
    wbr
    #
    @4
    @56
    @69
    @70
    @57
    cC
    @58
    iddvdsexp
    sylan
    @11
    @59
    cC
    cdvds
    breq2
    syl5ibrcom
    rexlimdva
    adantr
    adantl
    adantr
    @7
    @67
    @62
    wi
    @13
    @7
    @52
    @67
    @15
    @7
    @52
    @67
    wa
    #
    cC
    @10
    @11
    cmin
    co
    #
    cdvds
    wbr
    #
    @15
    @7
    @56
    @32
    @48
    w3a
    #
    @71
    @73
    wi
    @7
    @56
    @49
    wa
    @74
    @3
    @49
    @6
    @56
    @51
    @4
    @56
    @5
    @57
    adantr
    anim12ci
    @56
    @32
    @48
    3anass
    sylibr
    cC
    @10
    @11
    dvds2sub
    syl
    @3
    @73
    @15
    wi
    @6
    @3
    @73
    @15
    @3
    @72
    @14
    cC
    cdvds
    @3
    @72
    cB
    cB
    caddc
    co
    #
    @14
    @3
    cA
    cB
    cB
    @0
    @1
    @17
    @2
    @20
    3ad2ant1
    @1
    @0
    @18
    @2
    @21
    3ad2ant2
    #
    @76
    pnncand
    @1
    @0
    @75
    @14
    wceq
    @2
    @1
    @14
    @75
    @1
    cB
    @21
    2timesd
    eqcomd
    3ad2ant2
    eqtrd
    breq2d
    biimpd
    adantr
    syld
    expcomd
    adantr
    syld
    mpd
    syld
    mpd
    ex
    sylbid
end
