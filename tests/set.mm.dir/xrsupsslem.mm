include "cxr.mm"
include "wss.mm"
include "cr.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "wn.mm"
include "wral.mm"
include "wrex.mm"
include "wi.mm"
include "wa.mm"
include "cpnf.mm"
include "wcel.mm"
include "c0.mm"
include "wceq.mm"
include "raleq.mm"
include "rexeq.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "anbi12d.mm"
include "rexbidv.mm"
include "wne.mm"
include "cle.mm"
include "w3a.mm"
include "sup3.mm"
include "rexr.mm"
include "anim1i.mm"
include "reximi2.mm"
include "syl.mm"
include "cmnf.mm"
include "w3o.mm"
include "elxr.mm"
include "simpr.mm"
include "pnfnlt.mm"
include "adantr.mm"
include "wb.mm"
include "breq1.mm"
include "notbid.mm"
include "adantl.mm"
include "mpbird.mm"
include "pm2.21d.mm"
include "ex.mm"
include "ad2antlr.mm"
include "wex.mm"
include "ssel.mm"
include "mnflt.mm"
include "syl6.mm"
include "ancld.mm"
include "eximdv.mm"
include "n0.mm"
include "df-rex.mm"
include "3imtr4g.mm"
include "imp.mm"
include "a1d.mm"
include "ad2antrr.mm"
include "imbi12d.mm"
include "3jaod.mm"
include "syl5bi.mm"
include "ralimdv2.mm"
include "anim2d.mm"
include "reximdva.mm"
include "3adant3.mm"
include "mpd.mm"
include "3expa.mm"
include "ralnex.mm"
include "rexnal.mm"
include "ssel2.mm"
include "letric.mm"
include "ord.mm"
include "sylan.mm"
include "an32s.mm"
include "syl5bir.mm"
include "ralimdva.mm"
include "sylan2br.mm"
include "breq2.mm"
include "cbvrexv.mm"
include "ralbii.mm"
include "sylib.mm"
include "pnfxr.mm"
include "ralrimiv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "peano2re.mm"
include "rspcva.mm"
include "adantrr.mm"
include "ancoms.mm"
include "sylan2.mm"
include "ltp1.mm"
include "ancli.mm"
include "ltletr.mm"
include "mpand.mm"
include "adantll.mm"
include "exp31.mm"
include "a1dd.mm"
include "com4r.mm"
include "xrltnr.mm"
include "ax-mp.mm"
include "mtbiri.mm"
include "2a1d.mm"
include "cc0.mm"
include "0re.mm"
include "mpan.mm"
include "mpan9.mm"
include "syl5ibr.mm"
include "expd.mm"
include "3jaoi.mm"
include "sylbi.mm"
include "com13.mm"
include "jca.mm"
include "imbi1d.mm"
include "rspcev.mm"
include "sylancr.mm"
include "syldan.mm"
include "adantlr.mm"
include "pm2.61dan.mm"
include "mnfxr.mm"
include "ral0.mm"
include "nltmnf.mm"
include "rgen.mm"
include "pm3.2i.mm"
include "mp2an.mm"
include "a1i.mm"
include "pm2.61ne.mm"
include "ralrimivw.mm"
include "anim12i.mm"
include "jaodan.mm"

theorem xrsupsslem
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let vw: setvar w
  let cB: class B

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint B w
  assert |- ( ( A C_ RR* /\ ( A C_ RR \/ +oo e. A ) ) -> E. x e. RR* ( A. y e. A -. x < y /\ A. y e. RR* ( y < x -> E. z e. A y < z ) ) )

  proof
    cA
    cxr
    wss
    #
    cA
    cr
    wss
    #
    vx
    cv
    #
    vy
    cv
    #
    clt
    wbr
    #
    wn
    #
    vy
    cA
    wral
    #
    @3
    @2
    clt
    wbr
    #
    @3
    vz
    cv
    #
    clt
    wbr
    #
    vz
    cA
    wrex
    #
    wi
    #
    vy
    cxr
    wral
    #
    wa
    #
    vx
    cxr
    wrex
    #
    cpnf
    cA
    wcel
    #
    @1
    @14
    @0
    @1
    @14
    @5
    vy
    c0
    wral
    #
    @7
    @9
    vz
    c0
    wrex
    #
    wi
    #
    vy
    cxr
    wral
    #
    wa
    #
    vx
    cxr
    wrex
    #
    cA
    c0
    cA
    c0
    wceq
    #
    @13
    @20
    vx
    cxr
    @22
    @6
    @16
    @12
    @19
    @5
    vy
    cA
    c0
    raleq
    @22
    @11
    @18
    vy
    cxr
    @22
    @10
    @17
    @7
    @9
    vz
    cA
    c0
    rexeq
    imbi2d
    ralbidv
    anbi12d
    rexbidv
    @1
    cA
    c0
    wne
    #
    wa
    #
    @3
    @2
    cle
    wbr
    #
    vy
    cA
    wral
    #
    vx
    cr
    wrex
    #
    @14
    @1
    @23
    @27
    @14
    @1
    @23
    @27
    w3a
    #
    @6
    @11
    vy
    cr
    wral
    #
    wa
    #
    vx
    cxr
    wrex
    #
    @14
    @28
    @30
    vx
    cr
    wrex
    @31
    vx
    vy
    vz
    cA
    sup3
    @30
    @30
    vx
    cr
    cxr
    @2
    cr
    wcel
    #
    @2
    cxr
    wcel
    #
    @30
    @2
    rexr
    anim1i
    reximi2
    syl
    @1
    @23
    @31
    @14
    wi
    @27
    @24
    @30
    @13
    vx
    cxr
    @24
    @33
    wa
    #
    @29
    @12
    @6
    @34
    @11
    @11
    vy
    cr
    cxr
    @34
    @3
    cr
    wcel
    #
    @11
    wi
    #
    @3
    cxr
    wcel
    #
    @11
    wi
    @37
    @35
    @3
    cpnf
    wceq
    #
    @3
    cmnf
    wceq
    #
    w3o
    #
    @34
    @36
    wa
    #
    @11
    @3
    elxr
    #
    @41
    @35
    @11
    @38
    @39
    @34
    @36
    simpr
    @33
    @38
    @11
    wi
    @24
    @36
    @33
    @38
    @11
    @33
    @38
    wa
    #
    @7
    @10
    @43
    @7
    wn
    #
    cpnf
    @2
    clt
    wbr
    #
    wn
    #
    @33
    @46
    @38
    @2
    pnfnlt
    adantr
    @38
    @44
    @46
    wb
    @33
    @38
    @7
    @45
    @3
    cpnf
    @2
    clt
    breq1
    notbid
    adantl
    mpbird
    pm2.21d
    ex
    ad2antlr
    @34
    @39
    @11
    wi
    @36
    @34
    @39
    @11
    @34
    @39
    wa
    @11
    cmnf
    @2
    clt
    wbr
    #
    cmnf
    @8
    clt
    wbr
    #
    vz
    cA
    wrex
    #
    wi
    #
    @24
    @50
    @33
    @39
    @24
    @49
    @47
    @1
    @23
    @49
    @1
    @8
    cA
    wcel
    #
    vz
    wex
    @51
    @48
    wa
    #
    vz
    wex
    @23
    @49
    @1
    @51
    @52
    vz
    @1
    @51
    @48
    @1
    @51
    @8
    cr
    wcel
    #
    @48
    cA
    cr
    @8
    ssel
    @8
    mnflt
    #
    syl6
    ancld
    eximdv
    vz
    cA
    n0
    @48
    vz
    cA
    df-rex
    3imtr4g
    imp
    a1d
    ad2antrr
    @39
    @11
    @50
    wb
    @34
    @39
    @7
    @47
    @10
    @49
    @3
    cmnf
    @2
    clt
    breq1
    @39
    @9
    @48
    vz
    cA
    @3
    cmnf
    @8
    clt
    breq1
    rexbidv
    #
    imbi12d
    adantl
    mpbird
    ex
    adantr
    3jaod
    syl5bi
    ex
    ralimdv2
    anim2d
    reximdva
    3adant3
    mpd
    3expa
    @1
    @27
    wn
    #
    @14
    @23
    @1
    @56
    @2
    @8
    cle
    wbr
    #
    vz
    cA
    wrex
    #
    vx
    cr
    wral
    #
    @14
    @1
    @56
    wa
    @2
    @3
    cle
    wbr
    #
    vy
    cA
    wrex
    #
    vx
    cr
    wral
    #
    @59
    @56
    @1
    @26
    wn
    #
    vx
    cr
    wral
    #
    @62
    @26
    vx
    cr
    ralnex
    @1
    @64
    @62
    @1
    @63
    @61
    vx
    cr
    @63
    @25
    wn
    #
    vy
    cA
    wrex
    @1
    @32
    wa
    #
    @61
    @25
    vy
    cA
    rexnal
    @66
    @65
    @60
    vy
    cA
    @1
    @3
    cA
    wcel
    #
    @32
    @65
    @60
    wi
    #
    @1
    @67
    wa
    @35
    @32
    @68
    cA
    cr
    @3
    ssel2
    @35
    @32
    wa
    @25
    @60
    @3
    @2
    letric
    ord
    sylan
    an32s
    reximdva
    syl5bir
    ralimdva
    imp
    sylan2br
    @61
    @58
    vx
    cr
    @60
    @57
    vy
    vz
    cA
    @3
    @8
    @2
    cle
    breq2
    cbvrexv
    ralbii
    sylib
    @1
    @59
    wa
    #
    cpnf
    cxr
    wcel
    #
    cpnf
    @3
    clt
    wbr
    #
    wn
    #
    vy
    cA
    wral
    #
    @3
    cpnf
    clt
    wbr
    #
    @10
    wi
    #
    vy
    cxr
    wral
    #
    wa
    #
    @14
    pnfxr
    @69
    @73
    @76
    @1
    @73
    @59
    @1
    @72
    vy
    cA
    @1
    @67
    @35
    @72
    cA
    cr
    @3
    ssel
    @35
    @37
    @72
    @3
    rexr
    @3
    pnfnlt
    #
    syl
    syl6
    ralrimiv
    adantr
    @69
    @75
    vy
    cxr
    @1
    @59
    @37
    @75
    wi
    @37
    @59
    @1
    @75
    @37
    @40
    @59
    @1
    @75
    wi
    wi
    #
    @42
    @35
    @79
    @38
    @39
    @59
    @1
    @74
    @35
    @10
    @59
    @1
    @35
    @10
    wi
    @74
    @59
    @1
    @35
    @10
    @59
    @1
    wa
    #
    @35
    wa
    @3
    c1
    caddc
    co
    #
    @8
    cle
    wbr
    #
    vz
    cA
    wrex
    #
    @10
    @35
    @80
    @81
    cr
    wcel
    #
    @83
    @3
    peano2re
    #
    @84
    @80
    @83
    @84
    @59
    @83
    @1
    @58
    @83
    vx
    @81
    cr
    @2
    @81
    wceq
    @57
    @82
    vz
    cA
    @2
    @81
    @8
    cle
    breq1
    rexbidv
    rspcva
    adantrr
    ancoms
    sylan2
    @1
    @35
    @83
    @10
    wi
    @59
    @1
    @35
    wa
    @82
    @9
    vz
    cA
    @1
    @51
    @35
    @82
    @9
    wi
    #
    @1
    @51
    wa
    #
    @53
    @35
    @86
    cA
    cr
    @8
    ssel2
    #
    @35
    @53
    @86
    @35
    @53
    wa
    @3
    @81
    clt
    wbr
    #
    @82
    @9
    @35
    @89
    @53
    @3
    ltp1
    adantr
    @35
    @35
    @84
    wa
    @53
    @89
    @82
    wa
    @9
    wi
    #
    @35
    @84
    @85
    ancli
    @35
    @84
    @53
    @90
    @3
    @81
    @8
    ltletr
    3expa
    sylan
    mpand
    ancoms
    sylan
    an32s
    reximdva
    adantll
    mpd
    exp31
    a1dd
    com4r
    @38
    @75
    @59
    @1
    @38
    @74
    @10
    @38
    @74
    cpnf
    cpnf
    clt
    wbr
    #
    @70
    @91
    wn
    pnfxr
    cpnf
    xrltnr
    ax-mp
    @3
    cpnf
    cpnf
    clt
    breq1
    mtbiri
    pm2.21d
    2a1d
    @39
    @59
    @1
    @75
    @39
    @80
    @10
    @74
    @80
    @10
    @39
    @49
    @59
    cc0
    @8
    cle
    wbr
    #
    vz
    cA
    wrex
    #
    @1
    @49
    cc0
    cr
    wcel
    @59
    @93
    0re
    @58
    @93
    vx
    cc0
    cr
    @2
    cc0
    wceq
    @57
    @92
    vz
    cA
    @2
    cc0
    @8
    cle
    breq1
    rexbidv
    rspcva
    mpan
    @1
    @92
    @48
    vz
    cA
    @87
    @48
    @92
    @87
    @53
    @48
    @88
    @54
    syl
    a1d
    reximdva
    mpan9
    @55
    syl5ibr
    a1dd
    expd
    3jaoi
    sylbi
    com13
    imp
    ralrimiv
    jca
    @13
    @77
    vx
    cpnf
    cxr
    @2
    cpnf
    wceq
    #
    @6
    @73
    @12
    @76
    @94
    @5
    @72
    vy
    cA
    @94
    @4
    @71
    @2
    cpnf
    @3
    clt
    breq1
    notbid
    ralbidv
    @94
    @11
    @75
    vy
    cxr
    @94
    @7
    @74
    @10
    @2
    cpnf
    @3
    clt
    breq2
    imbi1d
    ralbidv
    anbi12d
    rspcev
    #
    sylancr
    syldan
    adantlr
    pm2.61dan
    @21
    @1
    cmnf
    cxr
    wcel
    cmnf
    @3
    clt
    wbr
    #
    wn
    #
    vy
    c0
    wral
    #
    @3
    cmnf
    clt
    wbr
    #
    @17
    wi
    #
    vy
    cxr
    wral
    #
    wa
    #
    @21
    mnfxr
    @98
    @101
    @97
    vy
    ral0
    @100
    vy
    cxr
    @37
    @99
    @17
    @3
    nltmnf
    pm2.21d
    rgen
    pm3.2i
    @20
    @102
    vx
    cmnf
    cxr
    @2
    cmnf
    wceq
    #
    @16
    @98
    @19
    @101
    @103
    @5
    @97
    vy
    c0
    @103
    @4
    @96
    @2
    cmnf
    @3
    clt
    breq1
    notbid
    ralbidv
    @103
    @18
    @100
    vy
    cxr
    @103
    @7
    @99
    @17
    @2
    cmnf
    @3
    clt
    breq2
    imbi1d
    ralbidv
    anbi12d
    rspcev
    mp2an
    a1i
    pm2.61ne
    adantl
    @0
    @15
    wa
    @70
    @77
    @14
    pnfxr
    @0
    @73
    @15
    @76
    @0
    @72
    vy
    cA
    @0
    @67
    @37
    @72
    cA
    cxr
    @3
    ssel
    @78
    syl6
    ralrimiv
    @15
    @75
    vy
    cxr
    @15
    @74
    @10
    @9
    @74
    vz
    cpnf
    cA
    @8
    cpnf
    @3
    clt
    breq2
    rspcev
    ex
    ralrimivw
    anim12i
    @95
    sylancr
    jaodan
end
