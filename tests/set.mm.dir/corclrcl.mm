include "crelexp.mm"
include "cc0.mm"
include "c1.mm"
include "cpr.mm"
include "crcl.mm"
include "dfrcl4.mm"
include "prex.mm"
include "cun.mm"
include "unidm.mm"
include "eqcomi.mm"
include "cv.mm"
include "co.mm"
include "ciun.mm"
include "csn.mm"
include "oveq2.mm"
include "cbviunv.mm"
include "1ex.mm"
include "iunxsn.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "ovex.mm"
include "iunex.mm"
include "relexp1g.mm"
include "ax-mp.mm"
include "eqtri.mm"
include "wss.mm"
include "snsspr2.mm"
include "iunss1.mm"
include "eqsstri.mm"
include "c0ex.mm"
include "prid1.mm"
include "ssiun2s.mm"
include "eqimssi.mm"
include "unss12.mm"
include "mp2an.mm"
include "df-pr.mm"
include "iuneq1.mm"
include "iunxun.mm"
include "cn0.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "vex.mm"
include "0nn0.mm"
include "1nn0.mm"
include "prssi.mm"
include "inidm.mm"
include "eleqtrri.mm"
include "ne0ii.mm"
include "iunrelexp0.mm"
include "mp3an.mm"
include "uneq12i.mm"
include "3sstr4i.mm"
include "comptiunov2i.mm"

theorem corclrcl
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k


  assert |- ( r* o. r* ) = r*

  proof
    vi
    vj
    vk
    crelexp
    cc0
    c1
    cpr
    #
    @0
    @0
    crcl
    crcl
    crcl
    va
    vb
    vc
    vd
    vi
    va
    dfrcl4
    vj
    vb
    dfrcl4
    vk
    vc
    dfrcl4
    cc0
    c1
    prex
    #
    @1
    @0
    @0
    cun
    #
    @0
    @0
    unidm
    eqcomi
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
    c1
    csn
    #
    vj
    @0
    @3
    vj
    cv
    #
    crelexp
    co
    #
    ciun
    #
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
    @12
    ciun
    #
    @6
    @10
    @13
    vk
    vj
    @0
    @5
    @9
    @4
    @8
    @3
    crelexp
    oveq2
    cbviunv
    @13
    @10
    @13
    @10
    c1
    crelexp
    co
    #
    @10
    vi
    c1
    @12
    @15
    1ex
    @11
    c1
    @10
    crelexp
    oveq2
    iunxsn
    @10
    cvv
    wcel
    @15
    @10
    wceq
    vj
    @0
    @9
    @1
    @3
    @8
    crelexp
    ovex
    iunex
    @10
    cvv
    relexp1g
    ax-mp
    eqtri
    #
    eqcomi
    eqtri
    @7
    @0
    wss
    @13
    @14
    wss
    cc0
    c1
    snsspr2
    vi
    @7
    @0
    @12
    iunss1
    ax-mp
    eqsstri
    #
    @17
    @3
    cc0
    crelexp
    co
    #
    @10
    cun
    #
    @6
    @6
    cun
    #
    @14
    vk
    @2
    @5
    ciun
    @18
    @6
    wss
    #
    @10
    @6
    wss
    @19
    @20
    wss
    cc0
    @0
    wcel
    @21
    cc0
    c1
    c0ex
    prid1
    #
    vk
    @0
    @5
    cc0
    @18
    @4
    cc0
    @3
    crelexp
    oveq2
    ssiun2s
    ax-mp
    @10
    @6
    vj
    vk
    @0
    @9
    @5
    @8
    @4
    @3
    crelexp
    oveq2
    cbviunv
    eqimssi
    @18
    @6
    @10
    @6
    unss12
    mp2an
    @14
    vi
    cc0
    csn
    #
    @7
    cun
    #
    @12
    ciun
    #
    @19
    @0
    @24
    wceq
    @14
    @25
    wceq
    cc0
    c1
    df-pr
    vi
    @0
    @24
    @12
    iuneq1
    ax-mp
    @25
    vi
    @23
    @12
    ciun
    #
    @13
    cun
    @19
    vi
    @23
    @7
    @12
    iunxun
    @26
    @18
    @13
    @10
    @26
    @10
    cc0
    crelexp
    co
    #
    @18
    vi
    cc0
    @12
    @27
    c0ex
    @11
    cc0
    @10
    crelexp
    oveq2
    iunxsn
    @3
    cvv
    wcel
    @0
    cn0
    wss
    #
    @0
    @0
    cin
    #
    c0
    wne
    @27
    @18
    wceq
    vd
    vex
    cc0
    cn0
    wcel
    c1
    cn0
    wcel
    @28
    0nn0
    1nn0
    cc0
    c1
    cn0
    prssi
    mp2an
    cc0
    @29
    cc0
    @0
    @29
    @22
    @0
    inidm
    eleqtrri
    ne0ii
    vj
    @3
    cvv
    @0
    iunrelexp0
    mp3an
    eqtri
    @16
    uneq12i
    eqtri
    eqtri
    vk
    @0
    @0
    @5
    iunxun
    3sstr4i
    comptiunov2i
end
