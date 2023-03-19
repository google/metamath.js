include "cusgr.mm"
include "wcel.mm"
include "wne.mm"
include "w3a.mm"
include "cvtx.mm"
include "cfv.mm"
include "cpr.mm"
include "wceq.mm"
include "wa.mm"
include "cfrgr.mm"
include "wnel.mm"
include "wi.mm"
include "cv.mm"
include "cedg.mm"
include "wss.mm"
include "wreu.mm"
include "csn.mm"
include "cdif.mm"
include "wral.mm"
include "wn.mm"
include "wrex.mm"
include "wo.mm"
include "neirr.mm"
include "eqid.mm"
include "usgredgne.mm"
include "ex.mm"
include "mtoi.mm"
include "adantl.mm"
include "intnanrd.mm"
include "prex.mm"
include "prss.mm"
include "sylnib.mm"
include "intnand.mm"
include "ioran.mm"
include "sylanbrc.mm"
include "wb.mm"
include "preq1.mm"
include "preq12d.mm"
include "sseq1d.mm"
include "rexprg.mm"
include "3adant3.mm"
include "adantr.mm"
include "mtbird.mm"
include "reurex.mm"
include "nsyl.mm"
include "orcd.mm"
include "rexnal.mm"
include "bicomi.mm"
include "a1i.mm"
include "difprsn1.mm"
include "3ad2ant3.mm"
include "rexeqdv.mm"
include "preq2.mm"
include "preq2d.mm"
include "reubidv.mm"
include "notbid.mm"
include "rexsng.mm"
include "3ad2ant2.mm"
include "3bitrd.mm"
include "difprsn2.mm"
include "3ad2ant1.mm"
include "orbi12d.mm"
include "mpbird.mm"
include "sneq.mm"
include "difeq2d.mm"
include "preq1d.mm"
include "raleqbidv.mm"
include "sylib.mm"
include "adantlr.mm"
include "id.mm"
include "difeq1.mm"
include "reueq1.mm"
include "anbi2d.mm"
include "df-nel.mm"
include "frgrusgrfrcond.mm"
include "xchbinx.mm"
include "sylibr.mm"
include "expcom.mm"
include "frgrusgr.mm"
include "con3i.mm"
include "a1d.mm"
include "pm2.61i.mm"

theorem nfrgr2v
  let cA: class A
  let cB: class B
  let cG: class G
  let cX: class X
  let cY: class Y
  let vk: setvar k
  let vl: setvar l
  let vx: setvar x


  assert |- ( ( ( A e. X /\ B e. Y /\ A =/= B ) /\ ( Vtx ` G ) = { A , B } ) -> G e/ FriendGraph )

  proof
    cG
    cusgr
    wcel
    #
    cA
    cX
    wcel
    #
    cB
    cY
    wcel
    #
    cA
    cB
    wne
    #
    w3a
    #
    cG
    cvtx
    cfv
    #
    cA
    cB
    cpr
    #
    wceq
    #
    wa
    #
    cG
    cfrgr
    wnel
    #
    wi
    @8
    @0
    @9
    @8
    @0
    wa
    #
    @0
    vx
    cv
    #
    vk
    cv
    #
    cpr
    #
    @11
    vl
    cv
    #
    cpr
    #
    cpr
    #
    cG
    cedg
    cfv
    #
    wss
    #
    vx
    @5
    wreu
    #
    vl
    @5
    @12
    csn
    #
    cdif
    #
    wral
    #
    vk
    @5
    wral
    #
    wa
    #
    wn
    #
    @9
    @10
    @25
    @0
    @18
    vx
    @6
    wreu
    #
    vl
    @6
    @20
    cdif
    #
    wral
    #
    vk
    @6
    wral
    #
    wa
    #
    wn
    #
    @4
    @0
    @31
    @7
    @4
    @0
    wa
    #
    @29
    @0
    @32
    @28
    wn
    #
    vk
    @6
    wrex
    #
    @29
    wn
    @32
    @34
    @11
    cA
    cpr
    #
    @15
    cpr
    #
    @17
    wss
    #
    vx
    @6
    wreu
    #
    vl
    @6
    cA
    csn
    #
    cdif
    #
    wral
    #
    wn
    #
    @11
    cB
    cpr
    #
    @15
    cpr
    #
    @17
    wss
    #
    vx
    @6
    wreu
    #
    vl
    @6
    cB
    csn
    #
    cdif
    #
    wral
    #
    wn
    #
    wo
    #
    @32
    @51
    @35
    @43
    cpr
    #
    @17
    wss
    #
    vx
    @6
    wreu
    #
    wn
    #
    @43
    @35
    cpr
    #
    @17
    wss
    #
    vx
    @6
    wreu
    #
    wn
    #
    wo
    @32
    @55
    @59
    @32
    @53
    vx
    @6
    wrex
    #
    @54
    @32
    @60
    cA
    cA
    cpr
    #
    @6
    cpr
    #
    @17
    wss
    #
    cB
    cA
    cpr
    #
    cB
    cB
    cpr
    #
    cpr
    #
    @17
    wss
    #
    wo
    #
    @32
    @63
    wn
    @67
    wn
    @68
    wn
    @32
    @61
    @17
    wcel
    #
    @6
    @17
    wcel
    #
    wa
    @63
    @32
    @69
    @70
    @0
    @69
    wn
    @4
    @0
    @69
    cA
    cA
    wne
    #
    cA
    neirr
    @0
    @69
    @71
    @17
    cG
    cA
    cA
    @17
    eqid
    #
    usgredgne
    ex
    mtoi
    adantl
    intnanrd
    @61
    @6
    @17
    cA
    cA
    prex
    cA
    cB
    prex
    prss
    sylnib
    @32
    @64
    @17
    wcel
    #
    @65
    @17
    wcel
    #
    wa
    @67
    @32
    @74
    @73
    @0
    @74
    wn
    @4
    @0
    @74
    cB
    cB
    wne
    #
    cB
    neirr
    @0
    @74
    @75
    @17
    cG
    cB
    cB
    @72
    usgredgne
    ex
    mtoi
    adantl
    intnand
    @64
    @65
    @17
    cB
    cA
    prex
    cB
    cB
    prex
    prss
    sylnib
    @63
    @67
    ioran
    sylanbrc
    @4
    @60
    @68
    wb
    #
    @0
    @1
    @2
    @76
    @3
    @53
    @63
    @67
    vx
    cA
    cB
    cX
    cY
    @11
    cA
    wceq
    #
    @52
    @62
    @17
    @77
    @35
    @61
    @43
    @6
    @11
    cA
    cA
    preq1
    @11
    cA
    cB
    preq1
    preq12d
    sseq1d
    @11
    cB
    wceq
    #
    @52
    @66
    @17
    @78
    @35
    @64
    @43
    @65
    @11
    cB
    cA
    preq1
    @11
    cB
    cB
    preq1
    preq12d
    sseq1d
    rexprg
    3adant3
    adantr
    mtbird
    @53
    vx
    @6
    reurex
    nsyl
    orcd
    @32
    @42
    @55
    @50
    @59
    @32
    @42
    @38
    wn
    #
    vl
    @40
    wrex
    #
    @79
    vl
    @47
    wrex
    #
    @55
    @42
    @80
    wb
    @32
    @80
    @42
    @38
    vl
    @40
    rexnal
    bicomi
    a1i
    @32
    @79
    vl
    @40
    @47
    @4
    @40
    @47
    wceq
    #
    @0
    @3
    @1
    @82
    @2
    cA
    cB
    difprsn1
    3ad2ant3
    adantr
    rexeqdv
    @4
    @81
    @55
    wb
    #
    @0
    @2
    @1
    @83
    @3
    @79
    @55
    vl
    cB
    cY
    @14
    cB
    wceq
    #
    @38
    @54
    @84
    @37
    @53
    vx
    @6
    @84
    @36
    @52
    @17
    @84
    @15
    @43
    @35
    @14
    cB
    @11
    preq2
    preq2d
    sseq1d
    reubidv
    notbid
    rexsng
    3ad2ant2
    adantr
    3bitrd
    @32
    @50
    @46
    wn
    #
    vl
    @48
    wrex
    #
    @85
    vl
    @39
    wrex
    #
    @59
    @50
    @86
    wb
    @32
    @86
    @50
    @46
    vl
    @48
    rexnal
    bicomi
    a1i
    @32
    @85
    vl
    @48
    @39
    @4
    @48
    @39
    wceq
    #
    @0
    @3
    @1
    @88
    @2
    cA
    cB
    difprsn2
    3ad2ant3
    adantr
    rexeqdv
    @4
    @87
    @59
    wb
    #
    @0
    @1
    @2
    @89
    @3
    @85
    @59
    vl
    cA
    cX
    @14
    cA
    wceq
    #
    @46
    @58
    @90
    @45
    @57
    vx
    @6
    @90
    @44
    @56
    @17
    @90
    @15
    @35
    @43
    @14
    cA
    @11
    preq2
    preq2d
    sseq1d
    reubidv
    notbid
    rexsng
    3ad2ant1
    adantr
    3bitrd
    orbi12d
    mpbird
    @4
    @34
    @51
    wb
    #
    @0
    @1
    @2
    @91
    @3
    @33
    @42
    @50
    vk
    cA
    cB
    cX
    cY
    @12
    cA
    wceq
    #
    @28
    @41
    @92
    @26
    @38
    vl
    @27
    @40
    @92
    @20
    @39
    @6
    @12
    cA
    sneq
    difeq2d
    @92
    @18
    @37
    vx
    @6
    @92
    @16
    @36
    @17
    @92
    @13
    @35
    @15
    @12
    cA
    @11
    preq2
    preq1d
    sseq1d
    reubidv
    raleqbidv
    notbid
    @12
    cB
    wceq
    #
    @28
    @49
    @93
    @26
    @46
    vl
    @27
    @48
    @93
    @20
    @47
    @6
    @12
    cB
    sneq
    difeq2d
    @93
    @18
    @45
    vx
    @6
    @93
    @16
    @44
    @17
    @93
    @13
    @43
    @15
    @12
    cB
    @11
    preq2
    preq1d
    sseq1d
    reubidv
    raleqbidv
    notbid
    rexprg
    3adant3
    adantr
    mpbird
    @28
    vk
    @6
    rexnal
    sylib
    intnand
    adantlr
    @8
    @25
    @31
    wb
    #
    @0
    @7
    @94
    @4
    @7
    @24
    @30
    @7
    @23
    @29
    @0
    @7
    @22
    @28
    vk
    @5
    @6
    @7
    id
    @7
    @19
    @26
    vl
    @21
    @27
    @5
    @6
    @20
    difeq1
    @18
    vx
    @5
    @6
    reueq1
    raleqbidv
    raleqbidv
    anbi2d
    notbid
    adantl
    adantr
    mpbird
    @9
    cG
    cfrgr
    wcel
    #
    @24
    cG
    cfrgr
    df-nel
    #
    vx
    vk
    @17
    cG
    @5
    vl
    @5
    eqid
    @72
    frgrusgrfrcond
    xchbinx
    sylibr
    expcom
    @0
    wn
    #
    @9
    @8
    @97
    @95
    wn
    @9
    @95
    @0
    cG
    frgrusgr
    con3i
    @96
    sylibr
    a1d
    pm2.61i
end
