include "bj-c2uple.mm"
include "bj-c1upl.mm"
include "cdif.mm"
include "c0.mm"
include "wne.mm"
include "wpss.mm"
include "c1o.mm"
include "csn.mm"
include "bj-ctag.mm"
include "cxp.mm"
include "cun.mm"
include "wss.mm"
include "xpundi.mm"
include "difeq2i.mm"
include "cin.mm"
include "wceq.mm"
include "incom.mm"
include "bj-disjsn01.mm"
include "xpdisj1.mm"
include "ax-mp.mm"
include "eqtr3i.mm"
include "disjdif2.mm"
include "wa.mm"
include "bj-1ex.mm"
include "snnz.mm"
include "bj-tagn0.mm"
include "pm3.2i.mm"
include "xpnz.mm"
include "mpbi.mm"
include "eqnetri.mm"
include "eqnetrri.mm"
include "0pss.mm"
include "mpbir.mm"
include "ssun2.mm"
include "sscon.mm"
include "ssdif.mm"
include "sstri.mm"
include "df-bj-2upl.mm"
include "df-bj-1upl.mm"
include "uneq1i.mm"
include "eqtri.mm"
include "difeq1i.mm"
include "sseqtr4i.mm"
include "psssstr.mm"
include "mp2an.mm"
include "difn0.mm"

theorem bj-2upln1upl
  let cA: class A
  let cB: class B
  let cC: class C


  assert |- (| A ,, B |) =/= (| C |)

  proof
    cA
    cB
    bj-c2uple
    #
    cC
    bj-c1upl
    #
    cdif
    #
    c0
    wne
    #
    @0
    @1
    wne
    c0
    @2
    wpss
    #
    @3
    c0
    c1o
    csn
    #
    cB
    bj-ctag
    #
    cxp
    #
    c0
    csn
    #
    cA
    bj-ctag
    #
    cxp
    #
    @8
    cC
    bj-ctag
    #
    cxp
    #
    cun
    #
    cdif
    #
    wpss
    #
    @14
    @2
    wss
    @4
    @15
    @14
    c0
    wne
    @7
    @8
    @9
    @11
    cun
    #
    cxp
    #
    cdif
    #
    @14
    c0
    @17
    @13
    @7
    @8
    @9
    @11
    xpundi
    difeq2i
    @18
    @7
    c0
    @7
    @17
    cin
    #
    c0
    wceq
    @18
    @7
    wceq
    @17
    @7
    cin
    #
    @19
    c0
    @17
    @7
    incom
    @8
    @5
    cin
    c0
    wceq
    @20
    c0
    wceq
    bj-disjsn01
    @8
    @5
    @16
    @6
    xpdisj1
    ax-mp
    eqtr3i
    @7
    @17
    disjdif2
    ax-mp
    @5
    c0
    wne
    #
    @6
    c0
    wne
    #
    wa
    @7
    c0
    wne
    @21
    @22
    c1o
    bj-1ex
    snnz
    cB
    bj-tagn0
    pm3.2i
    @5
    @6
    xpnz
    mpbi
    eqnetri
    eqnetrri
    @14
    0pss
    mpbir
    @14
    @0
    @12
    cdif
    #
    @2
    @14
    @10
    @7
    cun
    #
    @12
    cdif
    #
    @23
    @14
    @7
    @12
    cdif
    #
    @25
    @12
    @13
    wss
    @14
    @26
    wss
    @12
    @10
    ssun2
    @12
    @13
    @7
    sscon
    ax-mp
    @7
    @24
    wss
    @26
    @25
    wss
    @7
    @10
    ssun2
    @7
    @24
    @12
    ssdif
    ax-mp
    sstri
    @0
    @24
    @12
    @0
    cA
    bj-c1upl
    #
    @7
    cun
    @24
    cA
    cB
    df-bj-2upl
    @27
    @10
    @7
    cA
    df-bj-1upl
    uneq1i
    eqtri
    difeq1i
    sseqtr4i
    @1
    @12
    @0
    cC
    df-bj-1upl
    difeq2i
    sseqtr4i
    c0
    @14
    @2
    psssstr
    mp2an
    @2
    0pss
    mpbi
    @0
    @1
    difn0
    ax-mp
end
