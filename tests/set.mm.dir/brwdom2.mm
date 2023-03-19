include "wcel.mm"
include "cvv.mm"
include "cwdom.mm"
include "wbr.mm"
include "cv.mm"
include "wfo.mm"
include "wex.mm"
include "cpw.mm"
include "wrex.mm"
include "wb.mm"
include "elex.mm"
include "c0.mm"
include "wceq.mm"
include "wa.mm"
include "0wdom.mm"
include "breq1.mm"
include "syl5ibrcom.mm"
include "imp.mm"
include "0elpw.mm"
include "wf1o.mm"
include "f1o0.mm"
include "f1ofo.mm"
include "0ex.mm"
include "foeq1.mm"
include "spcev.mm"
include "mp2b.mm"
include "foeq2.mm"
include "exbidv.mm"
include "rspcev.mm"
include "mp2an.mm"
include "foeq3.mm"
include "rexbidv.mm"
include "mpbiri.mm"
include "adantl.mm"
include "2thd.mm"
include "wne.mm"
include "brwdomn0.mm"
include "cbvexv.mm"
include "pwidg.mm"
include "ad2antrr.mm"
include "sylancom.mm"
include "ex.mm"
include "syl5bi.mm"
include "n0.mm"
include "biimpi.mm"
include "ad2antlr.mm"
include "cdif.mm"
include "csn.mm"
include "cxp.mm"
include "cun.mm"
include "vex.mm"
include "difexg.mm"
include "snex.mm"
include "xpexg.mm"
include "sylancl.mm"
include "unexg.mm"
include "sylancr.mm"
include "adantr.mm"
include "wfn.mm"
include "crn.mm"
include "cin.mm"
include "fofn.mm"
include "fnconstg.mm"
include "mp1i.mm"
include "disjdif.mm"
include "a1i.mm"
include "fnun.mm"
include "syl21anc.mm"
include "wss.mm"
include "elpwi.mm"
include "undif.mm"
include "sylib.mm"
include "ad2antrl.mm"
include "fneq2d.mm"
include "mpbid.mm"
include "rnun.mm"
include "forn.mm"
include "ad2antll.mm"
include "uneq1d.mm"
include "wf.mm"
include "fconst6g.mm"
include "frn.mm"
include "syl.mm"
include "ssequn2.mm"
include "eqtrd.mm"
include "syl5eq.mm"
include "df-fo.mm"
include "sylanbrc.mm"
include "spcegv.mm"
include "sylc.mm"
include "exlimddv.mm"
include "expr.mm"
include "exlimdv.mm"
include "rexlimdva.mm"
include "impbid.mm"
include "bitrd.mm"
include "pm2.61dane.mm"

theorem brwdom2
  let vy: setvar y
  let vz: setvar z
  let cV: class V
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vw: setvar w
  let cF: class F
  let cZ: class Z

  disjoint X y
  disjoint X z
  disjoint y z
  disjoint Y y
  disjoint Y z
  disjoint X x
  disjoint X w
  disjoint x y
  disjoint x z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint Y x
  disjoint Y w
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint Z x
  disjoint Z y
  disjoint Z z
  disjoint Z w
  assert |- ( Y e. V -> ( X ~<_* Y <-> E. y e. ~P Y E. z z : y -onto-> X ) )

  proof
    cY
    cV
    wcel
    cY
    cvv
    wcel
    #
    cX
    cY
    cwdom
    wbr
    #
    vy
    cv
    #
    cX
    vz
    cv
    #
    wfo
    #
    vz
    wex
    #
    vy
    cY
    cpw
    #
    wrex
    #
    wb
    #
    cY
    cV
    elex
    @0
    @8
    cX
    c0
    @0
    cX
    c0
    wceq
    #
    wa
    @1
    @7
    @0
    @9
    @1
    @0
    @1
    @9
    c0
    cY
    cwdom
    wbr
    cvv
    cY
    0wdom
    cX
    c0
    cY
    cwdom
    breq1
    syl5ibrcom
    imp
    @9
    @7
    @0
    @9
    @7
    @2
    c0
    @3
    wfo
    #
    vz
    wex
    #
    vy
    @6
    wrex
    #
    c0
    @6
    wcel
    c0
    c0
    @3
    wfo
    #
    vz
    wex
    #
    @12
    cY
    0elpw
    c0
    c0
    c0
    wf1o
    c0
    c0
    c0
    wfo
    #
    @14
    f1o0
    c0
    c0
    c0
    f1ofo
    @13
    @15
    vz
    c0
    0ex
    c0
    c0
    @3
    c0
    foeq1
    spcev
    mp2b
    @11
    @14
    vy
    c0
    @6
    @2
    c0
    wceq
    @10
    @13
    vz
    @2
    c0
    c0
    @3
    foeq2
    exbidv
    rspcev
    mp2an
    @9
    @5
    @11
    vy
    @6
    @9
    @4
    @10
    vz
    cX
    c0
    @2
    @3
    foeq3
    exbidv
    rexbidv
    mpbiri
    adantl
    2thd
    @0
    cX
    c0
    wne
    #
    wa
    #
    @1
    cY
    cX
    vx
    cv
    #
    wfo
    #
    vx
    wex
    #
    @7
    @16
    @1
    @20
    wb
    @0
    vx
    cX
    cY
    brwdomn0
    adantl
    @17
    @20
    @7
    @20
    cY
    cX
    @3
    wfo
    #
    vz
    wex
    #
    @17
    @7
    @19
    @21
    vx
    vz
    cY
    cX
    @18
    @3
    foeq1
    cbvexv
    @17
    @22
    @7
    @17
    @22
    cY
    @6
    wcel
    #
    @7
    @0
    @23
    @16
    @22
    cY
    cvv
    pwidg
    ad2antrr
    @5
    @22
    vy
    cY
    @6
    @2
    cY
    wceq
    @4
    @21
    vz
    @2
    cY
    cX
    @3
    foeq2
    exbidv
    rspcev
    sylancom
    ex
    syl5bi
    @17
    @5
    @20
    vy
    @6
    @17
    @2
    @6
    wcel
    #
    wa
    @4
    @20
    vz
    @17
    @24
    @4
    @20
    @17
    @24
    @4
    wa
    #
    wa
    #
    vw
    cv
    #
    cX
    wcel
    #
    @20
    vw
    @16
    @28
    vw
    wex
    #
    @0
    @25
    @16
    @29
    vw
    cX
    n0
    biimpi
    ad2antlr
    @26
    @28
    wa
    #
    @3
    cY
    @2
    cdif
    #
    @27
    csn
    #
    cxp
    #
    cun
    #
    cvv
    wcel
    #
    cY
    cX
    @34
    wfo
    #
    @20
    @17
    @35
    @25
    @28
    @0
    @35
    @16
    @0
    @3
    cvv
    wcel
    @33
    cvv
    wcel
    #
    @35
    vz
    vex
    @0
    @31
    cvv
    wcel
    @32
    cvv
    wcel
    @37
    cY
    @2
    cvv
    difexg
    @27
    snex
    @31
    @32
    cvv
    cvv
    xpexg
    sylancl
    @3
    @33
    cvv
    cvv
    unexg
    sylancr
    adantr
    ad2antrr
    @30
    @34
    cY
    wfn
    #
    @34
    crn
    #
    cX
    wceq
    @36
    @30
    @34
    @2
    @31
    cun
    #
    wfn
    #
    @38
    @30
    @3
    @2
    wfn
    #
    @33
    @31
    wfn
    #
    @2
    @31
    cin
    c0
    wceq
    #
    @41
    @25
    @42
    @17
    @28
    @4
    @42
    @24
    @2
    cX
    @3
    fofn
    adantl
    ad2antlr
    @27
    cvv
    wcel
    @43
    @30
    vw
    vex
    @31
    @27
    cvv
    fnconstg
    mp1i
    @44
    @30
    @2
    cY
    disjdif
    a1i
    @2
    @31
    @3
    @33
    fnun
    syl21anc
    @30
    @40
    cY
    @34
    @26
    @40
    cY
    wceq
    #
    @28
    @24
    @45
    @17
    @4
    @24
    @2
    cY
    wss
    @45
    @2
    cY
    elpwi
    @2
    cY
    undif
    sylib
    ad2antrl
    adantr
    fneq2d
    mpbid
    @30
    @39
    @3
    crn
    #
    @33
    crn
    #
    cun
    #
    cX
    @3
    @33
    rnun
    @30
    @48
    cX
    @47
    cun
    #
    cX
    @30
    @46
    cX
    @47
    @26
    @46
    cX
    wceq
    #
    @28
    @4
    @50
    @17
    @24
    @2
    cX
    @3
    forn
    ad2antll
    adantr
    uneq1d
    @30
    @47
    cX
    wss
    #
    @49
    cX
    wceq
    @28
    @51
    @26
    @28
    @31
    cX
    @33
    wf
    @51
    @31
    @27
    cX
    fconst6g
    @31
    cX
    @33
    frn
    syl
    adantl
    @47
    cX
    ssequn2
    sylib
    eqtrd
    syl5eq
    cY
    cX
    @34
    df-fo
    sylanbrc
    @19
    @36
    vx
    @34
    cvv
    cY
    cX
    @18
    @34
    foeq1
    spcegv
    sylc
    exlimddv
    expr
    exlimdv
    rexlimdva
    impbid
    bitrd
    pm2.61dane
    syl
end
