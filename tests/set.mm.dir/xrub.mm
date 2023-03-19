include "cxr.mm"
include "wss.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "wrex.mm"
include "wi.mm"
include "cr.mm"
include "wral.mm"
include "wceq.mm"
include "breq1.mm"
include "rexbidv.mm"
include "imbi12d.mm"
include "cbvralv.mm"
include "cpnf.mm"
include "cmnf.mm"
include "w3o.mm"
include "elxr.mm"
include "pm2.27.mm"
include "a1i.mm"
include "wn.mm"
include "pnfnlt.mm"
include "notbid.mm"
include "syl5ibr.mm"
include "pm2.21.mm"
include "syl6com.mm"
include "ad2antlr.mm"
include "a1dd.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "peano2rem.mm"
include "rspcv.mm"
include "syl.mm"
include "adantl.mm"
include "ltm1.mm"
include "id.mm"
include "syl5com.mm"
include "mnflt.mm"
include "rexr.mm"
include "ssel2.mm"
include "adantlr.mm"
include "mnfxr.mm"
include "xrlttr.mm"
include "mp3an1.mm"
include "syl2anc.mm"
include "mpand.mm"
include "reximdva.mm"
include "3syld.mm"
include "1re.mm"
include "ax-mp.mm"
include "ltpnf.mm"
include "breq2.mm"
include "mpbiri.mm"
include "mp3an12.mm"
include "mpani.mm"
include "sylan9r.mm"
include "syl5.mm"
include "xrltnr.mm"
include "mtbiri.mm"
include "pm2.21d.mm"
include "a1d.mm"
include "3jaodan.mm"
include "sylan2b.mm"
include "imp.mm"
include "syl5ibrcom.mm"
include "3jaod.mm"
include "syl5bi.mm"
include "com23.mm"
include "ralimdv2.mm"
include "ex.mm"
include "pm2.43d.mm"
include "imim1i.mm"
include "ralimi2.mm"
include "impbid1.mm"

theorem xrub
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vz: setvar z
  let vw: setvar w

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint x z
  disjoint w x
  disjoint y z
  disjoint w y
  disjoint w z
  disjoint A z
  disjoint A w
  disjoint B z
  disjoint B w
  assert |- ( ( A C_ RR* /\ B e. RR* ) -> ( A. x e. RR ( x < B -> E. y e. A x < y ) <-> A. x e. RR* ( x < B -> E. y e. A x < y ) ) )

  proof
    cA
    cxr
    wss
    #
    cB
    cxr
    wcel
    #
    wa
    #
    vx
    cv
    #
    cB
    clt
    wbr
    #
    @3
    vy
    cv
    #
    clt
    wbr
    #
    vy
    cA
    wrex
    #
    wi
    #
    vx
    cr
    wral
    #
    @8
    vx
    cxr
    wral
    #
    @2
    @9
    @10
    @9
    vz
    cv
    #
    cB
    clt
    wbr
    #
    @11
    @5
    clt
    wbr
    #
    vy
    cA
    wrex
    #
    wi
    #
    vz
    cr
    wral
    #
    @2
    @9
    @10
    wi
    #
    @8
    @15
    vx
    vz
    cr
    @3
    @11
    wceq
    #
    @4
    @12
    @7
    @14
    @3
    @11
    cB
    clt
    breq1
    @18
    @6
    @13
    vy
    cA
    @3
    @11
    @5
    clt
    breq1
    rexbidv
    imbi12d
    cbvralv
    @2
    @16
    @17
    @2
    @16
    wa
    #
    @8
    @8
    vx
    cr
    cxr
    @19
    @3
    cxr
    wcel
    #
    @3
    cr
    wcel
    #
    @8
    wi
    #
    @8
    @20
    @21
    @3
    cpnf
    wceq
    #
    @3
    cmnf
    wceq
    #
    w3o
    @19
    @22
    @8
    wi
    #
    @3
    elxr
    @19
    @21
    @25
    @23
    @24
    @21
    @25
    wi
    @19
    @21
    @8
    pm2.27
    a1i
    @19
    @23
    @8
    @22
    @1
    @23
    @8
    wi
    @0
    @16
    @23
    @1
    @4
    wn
    #
    @8
    @1
    @26
    @23
    cpnf
    cB
    clt
    wbr
    #
    wn
    cB
    pnfnlt
    @23
    @4
    @27
    @3
    cpnf
    cB
    clt
    breq1
    notbid
    syl5ibr
    @4
    @7
    pm2.21
    syl6com
    ad2antlr
    a1dd
    @19
    @24
    @8
    @22
    @19
    @8
    @24
    cmnf
    cB
    clt
    wbr
    #
    cmnf
    @5
    clt
    wbr
    #
    vy
    cA
    wrex
    #
    wi
    #
    @2
    @16
    @31
    @1
    @0
    cB
    cr
    wcel
    #
    cB
    cpnf
    wceq
    #
    cB
    cmnf
    wceq
    #
    w3o
    @16
    @31
    wi
    #
    cB
    elxr
    @0
    @32
    @35
    @33
    @34
    @0
    @32
    wa
    #
    @16
    @30
    @28
    @36
    @16
    cB
    c1
    cmin
    co
    #
    cB
    clt
    wbr
    #
    @37
    @5
    clt
    wbr
    #
    vy
    cA
    wrex
    #
    wi
    #
    @40
    @30
    @32
    @16
    @41
    wi
    #
    @0
    @32
    @37
    cr
    wcel
    #
    @42
    cB
    peano2rem
    #
    @15
    @41
    vz
    @37
    cr
    @11
    @37
    wceq
    #
    @12
    @38
    @14
    @40
    @11
    @37
    cB
    clt
    breq1
    @45
    @13
    @39
    vy
    cA
    @11
    @37
    @5
    clt
    breq1
    rexbidv
    imbi12d
    rspcv
    syl
    adantl
    @32
    @41
    @40
    wi
    @0
    @32
    @38
    @41
    @40
    cB
    ltm1
    @41
    id
    syl5com
    adantl
    @36
    @39
    @29
    vy
    cA
    @36
    @5
    cA
    wcel
    #
    wa
    #
    cmnf
    @37
    clt
    wbr
    #
    @39
    @29
    @47
    @43
    @48
    @32
    @43
    @0
    @46
    @44
    ad2antlr
    #
    @37
    mnflt
    syl
    @47
    @37
    cxr
    wcel
    #
    @5
    cxr
    wcel
    #
    @48
    @39
    wa
    @29
    wi
    #
    @47
    @43
    @50
    @49
    @37
    rexr
    syl
    @0
    @46
    @51
    @32
    cA
    cxr
    @5
    ssel2
    #
    adantlr
    cmnf
    cxr
    wcel
    #
    @50
    @51
    @52
    mnfxr
    cmnf
    @37
    @5
    xrlttr
    mp3an1
    syl2anc
    mpand
    reximdva
    3syld
    a1dd
    @0
    @33
    wa
    #
    @16
    @30
    @28
    @16
    c1
    cB
    clt
    wbr
    #
    c1
    @5
    clt
    wbr
    #
    vy
    cA
    wrex
    #
    wi
    #
    @55
    @30
    c1
    cr
    wcel
    #
    @16
    @59
    wi
    1re
    @15
    @59
    vz
    c1
    cr
    @11
    c1
    wceq
    #
    @12
    @56
    @14
    @58
    @11
    c1
    cB
    clt
    breq1
    @61
    @13
    @57
    vy
    cA
    @11
    c1
    @5
    clt
    breq1
    rexbidv
    imbi12d
    rspcv
    ax-mp
    @33
    @59
    @58
    @0
    @30
    @33
    @56
    @59
    @58
    @33
    @56
    c1
    cpnf
    clt
    wbr
    #
    @60
    @62
    1re
    c1
    ltpnf
    ax-mp
    cB
    cpnf
    c1
    clt
    breq2
    mpbiri
    @59
    id
    syl5com
    @0
    @57
    @29
    vy
    cA
    @0
    @46
    wa
    @51
    @57
    @29
    wi
    @53
    @51
    cmnf
    c1
    clt
    wbr
    #
    @57
    @29
    @60
    @63
    1re
    c1
    mnflt
    ax-mp
    @54
    c1
    cxr
    wcel
    #
    @51
    @63
    @57
    wa
    @29
    wi
    mnfxr
    @60
    @64
    1re
    c1
    rexr
    ax-mp
    cmnf
    c1
    @5
    xrlttr
    mp3an12
    mpani
    syl
    reximdva
    sylan9r
    syl5
    a1dd
    @0
    @34
    wa
    #
    @31
    @16
    @65
    @28
    @30
    @34
    @28
    wn
    @0
    @34
    @28
    cmnf
    cmnf
    clt
    wbr
    #
    @54
    @66
    wn
    mnfxr
    cmnf
    xrltnr
    ax-mp
    cB
    cmnf
    cmnf
    clt
    breq2
    mtbiri
    adantl
    pm2.21d
    a1d
    3jaodan
    sylan2b
    imp
    @24
    @4
    @28
    @7
    @30
    @3
    cmnf
    cB
    clt
    breq1
    @24
    @6
    @29
    vy
    cA
    @3
    cmnf
    @5
    clt
    breq1
    rexbidv
    imbi12d
    syl5ibrcom
    a1dd
    3jaod
    syl5bi
    com23
    ralimdv2
    ex
    syl5bi
    pm2.43d
    @8
    @8
    vx
    cxr
    cr
    @21
    @20
    @8
    @3
    rexr
    imim1i
    ralimi2
    impbid1
end
