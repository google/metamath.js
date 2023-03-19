include "cfrgr.mm"
include "wcel.mm"
include "wa.mm"
include "wne.mm"
include "cpr.mm"
include "wceq.mm"
include "wi.mm"
include "cusgr.mm"
include "frgrusgr.mm"
include "cvtx.mm"
include "cfv.mm"
include "cnbgr.mm"
include "co.mm"
include "eleq2i.mm"
include "nbusgreledg.mm"
include "biimpd.mm"
include "syl5bi.mm"
include "anim12d.mm"
include "imp.mm"
include "eqid.mm"
include "nbgrisvtx.mm"
include "eleq2s.mm"
include "anim12i.mm"
include "adantl.mm"
include "usgrpredgv.mm"
include "ad2ant2r.mm"
include "ax-1.mm"
include "2a1d.mm"
include "wnel.mm"
include "wn.mm"
include "w3a.mm"
include "simpll.mm"
include "simprrr.mm"
include "adantr.mm"
include "simprrl.mm"
include "necom.mm"
include "biimpi.mm"
include "3jca.mm"
include "simprll.mm"
include "simprlr.mm"
include "ad4ant14.mm"
include "prcom.mm"
include "eleq1i.mm"
include "anim1i.mm"
include "ancomd.mm"
include "anim2i.mm"
include "4cyclusnfrgr.mm"
include "sylc.mm"
include "df-nel.mm"
include "sylib.mm"
include "pm2.21d.mm"
include "ex.mm"
include "com23.mm"
include "exp41.mm"
include "com25.mm"
include "mpcom.mm"
include "com15.mm"
include "pm2.61ine.mm"
include "com13.mm"
include "nbgrcl.mm"
include "syl11.mm"
include "com34.mm"
include "impd.mm"
include "com14.mm"
include "mp2d.mm"
include "3imp.mm"

theorem frgrnbnb
  let cA: class A
  let cD: class D
  let cU: class U
  let cE: class E
  let cG: class G
  let cW: class W
  let cX: class X
  assume frgrnbnb.e: |- E = ( Edg ` G )
  assume frgrnbnb.n: |- D = ( G NeighbVtx X )


  assert |- ( ( G e. FriendGraph /\ ( U e. D /\ W e. D ) /\ U =/= W ) -> ( ( { U , A } e. E /\ { W , A } e. E ) -> A = X ) )

  proof
    cG
    cfrgr
    wcel
    #
    cU
    cD
    wcel
    #
    cW
    cD
    wcel
    #
    wa
    #
    cU
    cW
    wne
    #
    cU
    cA
    cpr
    cE
    wcel
    #
    cW
    cA
    cpr
    #
    cE
    wcel
    #
    wa
    #
    cA
    cX
    wceq
    #
    wi
    #
    cG
    cusgr
    wcel
    #
    @0
    @3
    @4
    @10
    wi
    #
    wi
    cG
    frgrusgr
    #
    @11
    @3
    @0
    @12
    @11
    @3
    @0
    @12
    wi
    #
    @11
    @3
    wa
    #
    cU
    cX
    cpr
    #
    cE
    wcel
    #
    cW
    cX
    cpr
    cE
    wcel
    #
    wa
    #
    cU
    cG
    cvtx
    cfv
    #
    wcel
    #
    cW
    @20
    wcel
    #
    wa
    #
    @14
    @11
    @3
    @19
    @11
    @1
    @17
    @2
    @18
    @1
    cU
    cG
    cX
    cnbgr
    co
    #
    wcel
    #
    @11
    @17
    cD
    @24
    cU
    frgrnbnb.n
    eleq2i
    @11
    @25
    @17
    cE
    cG
    cX
    cU
    frgrnbnb.e
    nbusgreledg
    biimpd
    syl5bi
    @2
    cW
    @24
    wcel
    #
    @11
    @18
    cD
    @24
    cW
    frgrnbnb.n
    eleq2i
    @11
    @26
    @18
    cE
    cG
    cX
    cW
    frgrnbnb.e
    nbusgreledg
    biimpd
    syl5bi
    anim12d
    imp
    @3
    @23
    @11
    @1
    @21
    @2
    @22
    @21
    cU
    @24
    cD
    cG
    cX
    cU
    @20
    @20
    eqid
    #
    nbgrisvtx
    frgrnbnb.n
    eleq2s
    @22
    cW
    @24
    cD
    cG
    cX
    cW
    @20
    @27
    nbgrisvtx
    frgrnbnb.n
    eleq2s
    anim12i
    adantl
    @4
    @19
    @23
    @0
    @15
    @10
    @4
    @19
    @23
    @0
    @15
    @10
    wi
    wi
    wi
    @15
    @23
    @0
    @4
    @19
    wa
    #
    @10
    @15
    @8
    @0
    @28
    @23
    @9
    @15
    @8
    @0
    @28
    @23
    @9
    wi
    wi
    #
    wi
    #
    @21
    cA
    @20
    wcel
    #
    wa
    #
    @15
    @8
    wa
    #
    @30
    @11
    @5
    @32
    @3
    @7
    cE
    cG
    cU
    cA
    @20
    frgrnbnb.e
    @27
    usgrpredgv
    ad2ant2r
    @31
    @33
    @30
    wi
    @21
    @31
    @15
    @8
    @30
    @31
    @15
    @0
    @8
    @29
    cX
    @20
    wcel
    #
    @31
    @0
    @8
    @29
    wi
    wi
    #
    @15
    @34
    @31
    @35
    @34
    @31
    wa
    #
    @23
    @8
    @28
    @0
    @9
    @36
    @23
    @8
    @28
    @0
    @9
    wi
    #
    wi
    wi
    @28
    @8
    @36
    @23
    wa
    #
    @37
    @4
    @19
    @8
    @38
    @37
    wi
    wi
    #
    @4
    @19
    @39
    wi
    #
    wi
    cA
    cX
    @9
    @39
    @4
    @19
    @9
    @37
    @8
    @38
    @9
    @0
    ax-1
    2a1d
    2a1d
    cA
    cX
    wne
    #
    @4
    @40
    @0
    @19
    @8
    @38
    @41
    @4
    wa
    #
    @9
    @11
    @0
    @19
    @8
    @38
    @42
    @9
    wi
    #
    wi
    wi
    wi
    @13
    @11
    @38
    @19
    @8
    @0
    @43
    @11
    @38
    @19
    @8
    @0
    @43
    wi
    @11
    @38
    wa
    #
    @19
    wa
    #
    @8
    wa
    #
    @42
    @0
    @9
    @46
    @42
    @37
    @46
    @42
    wa
    #
    @0
    @9
    @47
    cG
    cfrgr
    wnel
    #
    @0
    wn
    @47
    @11
    @22
    @21
    cW
    cU
    wne
    #
    w3a
    #
    @34
    @31
    cX
    cA
    wne
    #
    w3a
    #
    w3a
    #
    @18
    cX
    cU
    cpr
    #
    cE
    wcel
    #
    wa
    #
    @5
    cA
    cW
    cpr
    #
    cE
    wcel
    #
    wa
    #
    wa
    #
    @48
    @44
    @42
    @53
    @19
    @8
    @44
    @42
    wa
    #
    @11
    @50
    @52
    @11
    @38
    @42
    simpll
    @61
    @22
    @21
    @49
    @44
    @22
    @42
    @11
    @36
    @21
    @22
    simprrr
    adantr
    @44
    @21
    @42
    @11
    @36
    @21
    @22
    simprrl
    adantr
    @42
    @49
    @44
    @4
    @49
    @41
    @4
    @49
    cU
    cW
    necom
    biimpi
    adantl
    adantl
    3jca
    @61
    @34
    @31
    @51
    @44
    @34
    @42
    @11
    @34
    @31
    @23
    simprll
    adantr
    @44
    @31
    @42
    @11
    @34
    @31
    @23
    simprlr
    adantr
    @42
    @51
    @44
    @41
    @51
    @4
    @41
    @51
    cA
    cX
    necom
    biimpi
    adantr
    adantl
    3jca
    3jca
    ad4ant14
    @46
    @60
    @42
    @45
    @56
    @8
    @59
    @19
    @56
    @44
    @19
    @55
    @18
    @17
    @55
    @18
    @17
    @55
    @16
    @54
    cE
    cU
    cX
    prcom
    eleq1i
    biimpi
    anim1i
    ancomd
    adantl
    @7
    @58
    @5
    @7
    @58
    @6
    @57
    cE
    cW
    cA
    prcom
    eleq1i
    biimpi
    anim2i
    anim12i
    adantr
    cW
    cX
    cU
    cA
    cE
    cG
    @20
    @27
    frgrnbnb.e
    4cyclusnfrgr
    sylc
    cG
    cfrgr
    df-nel
    sylib
    pm2.21d
    ex
    com23
    exp41
    com25
    mpcom
    com15
    ex
    pm2.61ine
    imp
    com13
    ex
    com25
    ex
    @3
    @34
    @11
    @1
    @34
    @2
    @34
    cU
    @24
    cD
    cG
    cU
    @20
    cX
    @27
    nbgrcl
    frgrnbnb.n
    eleq2s
    adantr
    adantl
    syl11
    com34
    impd
    adantl
    mpcom
    ex
    com25
    com14
    ex
    com15
    mp2d
    ex
    com23
    mpcom
    3imp
end
