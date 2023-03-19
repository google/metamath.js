include "wcel.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "cun.mm"
include "csuc.mm"
include "cen.mm"
include "wbr.mm"
include "limenpsi.mm"
include "ensymd.mm"
include "cvv.mm"
include "0ex.mm"
include "en2sn.mm"
include "mpan.mm"
include "wa.mm"
include "cin.mm"
include "wceq.mm"
include "incom.mm"
include "disjdif.mm"
include "eqtri.mm"
include "wn.mm"
include "word.mm"
include "wlim.mm"
include "limord.mm"
include "ax-mp.mm"
include "ordirr.mm"
include "disjsn.mm"
include "mpbir.mm"
include "unen.mm"
include "mpanr12.mm"
include "syl2anc.mm"
include "wss.mm"
include "0ellim.mm"
include "snss.mm"
include "mpbi.mm"
include "undif.mm"
include "uncom.mm"
include "eqtr3i.mm"
include "df-suc.mm"
include "3brtr4g.mm"

theorem limensuci
  let cA: class A
  let cV: class V
  assume limensuci.1: |- Lim A


  assert |- ( A e. V -> A ~~ suc A )

  proof
    cA
    cV
    wcel
    #
    cA
    c0
    csn
    #
    cdif
    #
    @1
    cun
    #
    cA
    cA
    csn
    #
    cun
    #
    cA
    cA
    csuc
    cen
    @0
    @2
    cA
    cen
    wbr
    #
    @1
    @4
    cen
    wbr
    #
    @3
    @5
    cen
    wbr
    #
    @0
    cA
    @2
    cA
    cV
    limensuci.1
    limenpsi
    ensymd
    c0
    cvv
    wcel
    @0
    @7
    0ex
    c0
    cA
    cvv
    cV
    en2sn
    mpan
    @6
    @7
    wa
    @2
    @1
    cin
    #
    c0
    wceq
    cA
    @4
    cin
    c0
    wceq
    #
    @8
    @9
    @1
    @2
    cin
    c0
    @2
    @1
    incom
    @1
    cA
    disjdif
    eqtri
    @10
    cA
    cA
    wcel
    wn
    #
    cA
    word
    #
    @11
    cA
    wlim
    #
    @12
    limensuci.1
    cA
    limord
    ax-mp
    cA
    ordirr
    ax-mp
    cA
    cA
    disjsn
    mpbir
    @2
    cA
    @1
    @4
    unen
    mpanr12
    syl2anc
    @1
    @2
    cun
    #
    cA
    @3
    @1
    cA
    wss
    #
    @14
    cA
    wceq
    c0
    cA
    wcel
    #
    @15
    @13
    @16
    limensuci.1
    cA
    0ellim
    ax-mp
    c0
    cA
    0ex
    snss
    mpbi
    @1
    cA
    undif
    mpbi
    @1
    @2
    uncom
    eqtr3i
    cA
    df-suc
    3brtr4g
end
