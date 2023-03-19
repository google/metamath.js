include "crelexp.mm"
include "cc0.mm"
include "c1.mm"
include "cpr.mm"
include "cn.mm"
include "cn0.mm"
include "crcl.mm"
include "ctcl.mm"
include "crtcl.mm"
include "dfrcl4.mm"
include "dftrcl3.mm"
include "dfrtrcl3.mm"
include "prex.mm"
include "nnex.mm"
include "csn.mm"
include "cun.mm"
include "df-n0.mm"
include "uncom.mm"
include "df-pr.mm"
include "uneq1i.mm"
include "unass.mm"
include "wss.mm"
include "wceq.mm"
include "wcel.mm"
include "1nn.mm"
include "snssi.mm"
include "ax-mp.mm"
include "ssequn1.mm"
include "mpbi.mm"
include "uneq2i.mm"
include "3eqtrri.mm"
include "3eqtri.mm"
include "cv.mm"
include "co.mm"
include "ciun.mm"
include "oveq2.mm"
include "cbviunv.mm"
include "ss2iun.mm"
include "cvv.mm"
include "vex.mm"
include "relexp1g.mm"
include "ssiun2s.mm"
include "eqsstr3i.mm"
include "a1i.mm"
include "ovex.mm"
include "iunex.mm"
include "0nn0.mm"
include "1nn0.mm"
include "prssi.mm"
include "mp2an.mm"
include "sseli.mm"
include "relexpss1d.mm"
include "mprg.mm"
include "eqsstri.mm"
include "eqtr4i.mm"
include "1ex.mm"
include "prid2.mm"
include "c0ex.mm"
include "prid1.mm"
include "ssid.mm"
include "unss12.mm"
include "iuneq1.mm"
include "iunxun.mm"
include "iunxsn.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "nnssnn0.mm"
include "inelcm.mm"
include "iunrelexp0.mm"
include "mp3an.mm"
include "eqtri.mm"
include "uneq12i.mm"
include "3sstr4i.mm"
include "comptiunov2i.mm"

theorem corcltrcl
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k


  assert |- ( r* o. t+ ) = t*

  proof
    vi
    vj
    vk
    crelexp
    cc0
    c1
    cpr
    #
    cn
    cn0
    crcl
    ctcl
    crtcl
    va
    vb
    vc
    vd
    vi
    va
    dfrcl4
    vj
    vb
    dftrcl3
    vk
    vc
    dfrtrcl3
    cc0
    c1
    prex
    nnex
    cn0
    cn
    cc0
    csn
    #
    cun
    @1
    cn
    cun
    #
    @0
    cn
    cun
    #
    df-n0
    cn
    @1
    uncom
    @3
    @1
    c1
    csn
    #
    cun
    #
    cn
    cun
    @1
    @4
    cn
    cun
    #
    cun
    @2
    @0
    @5
    cn
    cc0
    c1
    df-pr
    #
    uneq1i
    @1
    @4
    cn
    unass
    @6
    cn
    @1
    @4
    cn
    wss
    #
    @6
    cn
    wceq
    c1
    cn
    wcel
    #
    @8
    1nn
    c1
    cn
    snssi
    ax-mp
    @4
    cn
    ssequn1
    mpbi
    uneq2i
    3eqtrri
    3eqtri
    vk
    @0
    vd
    cv
    #
    vk
    cv
    #
    crelexp
    co
    #
    ciun
    #
    vi
    @0
    @10
    vi
    cv
    #
    crelexp
    co
    #
    ciun
    #
    vi
    @0
    vj
    cn
    @10
    vj
    cv
    #
    crelexp
    co
    #
    ciun
    #
    @14
    crelexp
    co
    #
    ciun
    #
    vk
    vi
    @0
    @12
    @15
    @11
    @14
    @10
    crelexp
    oveq2
    cbviunv
    @15
    @20
    wss
    @16
    @21
    wss
    vi
    @0
    vi
    @0
    @15
    @20
    ss2iun
    @14
    @0
    wcel
    #
    @10
    @19
    @14
    @10
    @19
    wss
    @22
    @10
    @10
    c1
    crelexp
    co
    #
    @19
    @10
    cvv
    wcel
    #
    @23
    @10
    wceq
    vd
    vex
    #
    @10
    cvv
    relexp1g
    ax-mp
    @9
    @23
    @19
    wss
    1nn
    vj
    cn
    @18
    c1
    @23
    @17
    c1
    @10
    crelexp
    oveq2
    ssiun2s
    ax-mp
    eqsstr3i
    a1i
    @19
    cvv
    wcel
    #
    @22
    vj
    cn
    @18
    nnex
    @10
    @17
    crelexp
    ovex
    iunex
    #
    a1i
    @0
    cn0
    @14
    cc0
    cn0
    wcel
    c1
    cn0
    wcel
    @0
    cn0
    wss
    0nn0
    1nn0
    cc0
    c1
    cn0
    prssi
    mp2an
    sseli
    relexpss1d
    mprg
    eqsstri
    vk
    cn
    @12
    ciun
    #
    @19
    c1
    crelexp
    co
    #
    @21
    @28
    @19
    @29
    vk
    vj
    cn
    @12
    @18
    @11
    @17
    @10
    crelexp
    oveq2
    cbviunv
    #
    @26
    @29
    @19
    wceq
    @27
    @19
    cvv
    relexp1g
    ax-mp
    #
    eqtr4i
    c1
    @0
    wcel
    #
    @29
    @21
    wss
    cc0
    c1
    1ex
    prid2
    #
    vi
    @0
    @20
    c1
    @29
    @14
    c1
    @19
    crelexp
    oveq2
    #
    ssiun2s
    ax-mp
    eqsstri
    @10
    cc0
    crelexp
    co
    #
    @28
    cun
    #
    @13
    @28
    cun
    #
    @21
    vk
    @3
    @12
    ciun
    @35
    @13
    wss
    #
    @28
    @28
    wss
    @36
    @37
    wss
    cc0
    @0
    wcel
    @38
    cc0
    c1
    c0ex
    prid1
    vk
    @0
    @12
    cc0
    @35
    @11
    cc0
    @10
    crelexp
    oveq2
    ssiun2s
    ax-mp
    @28
    ssid
    @35
    @13
    @28
    @28
    unss12
    mp2an
    @21
    vi
    @5
    @20
    ciun
    #
    vi
    @1
    @20
    ciun
    #
    vi
    @4
    @20
    ciun
    #
    cun
    @36
    @0
    @5
    wceq
    @21
    @39
    wceq
    @7
    vi
    @0
    @5
    @20
    iuneq1
    ax-mp
    vi
    @1
    @4
    @20
    iunxun
    @40
    @35
    @41
    @28
    @40
    @19
    cc0
    crelexp
    co
    #
    @35
    vi
    cc0
    @20
    @42
    c0ex
    @14
    cc0
    @19
    crelexp
    oveq2
    iunxsn
    @24
    cn
    cn0
    wss
    @0
    cn
    cin
    c0
    wne
    #
    @42
    @35
    wceq
    @25
    nnssnn0
    @32
    @9
    @43
    @33
    1nn
    c1
    @0
    cn
    inelcm
    mp2an
    vj
    @10
    cvv
    cn
    iunrelexp0
    mp3an
    eqtri
    @41
    @29
    @28
    vi
    c1
    @20
    @29
    1ex
    @34
    iunxsn
    @29
    @19
    @28
    @31
    @30
    eqtr4i
    eqtri
    uneq12i
    3eqtri
    vk
    @0
    cn
    @12
    iunxun
    3sstr4i
    comptiunov2i
end
