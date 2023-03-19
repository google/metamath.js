include "cfin4.mm"
include "wcel.mm"
include "c1o.mm"
include "ccda.mm"
include "co.mm"
include "csdm.mm"
include "wbr.mm"
include "cdom.mm"
include "cen.mm"
include "wn.mm"
include "con0.mm"
include "1on.mm"
include "cdadom3.mm"
include "mpan2.mm"
include "c0.mm"
include "csn.mm"
include "cxp.mm"
include "wpss.mm"
include "cop.mm"
include "cun.mm"
include "ssun1.mm"
include "cvv.mm"
include "wceq.mm"
include "relen.mm"
include "brrelexi.mm"
include "cdaval.mm"
include "sylancl.mm"
include "syl5sseqr.mm"
include "0lt1o.mm"
include "elexi.mm"
include "snid.mm"
include "opelxpi.mm"
include "mp2an.mm"
include "elun2.mm"
include "mp1i.mm"
include "eleqtrrd.mm"
include "wne.mm"
include "1n0.mm"
include "opelxp2.mm"
include "elsni.mm"
include "syl.mm"
include "necon3ai.mm"
include "ssnelpssd.mm"
include "0ex.mm"
include "xpsneng.mm"
include "entr.mm"
include "mpancom.mm"
include "fin4i.mm"
include "syl2anc.mm"
include "fin4en1.mm"
include "mtod.mm"
include "con2i.mm"
include "brsdom.mm"
include "sylanbrc.mm"
include "com.mm"
include "sdomnen.mm"
include "infcda1.mm"
include "ensymd.mm"
include "nsyl.mm"
include "wb.mm"
include "relsdom.mm"
include "isfin4-2.mm"
include "mpbird.mm"
include "impbii.mm"

theorem isfin4-3
  let cA: class A


  assert |- ( A e. Fin4 <-> A ~< ( A +c 1o ) )

  proof
    cA
    cfin4
    wcel
    #
    cA
    cA
    c1o
    ccda
    co
    #
    csdm
    wbr
    #
    @0
    cA
    @1
    cdom
    wbr
    #
    cA
    @1
    cen
    wbr
    #
    wn
    @2
    @0
    c1o
    con0
    wcel
    #
    @3
    1on
    cA
    c1o
    cfin4
    con0
    cdadom3
    mpan2
    @4
    @0
    @4
    @0
    @1
    cfin4
    wcel
    #
    @4
    cA
    c0
    csn
    #
    cxp
    #
    @1
    wpss
    @8
    @1
    cen
    wbr
    #
    @6
    wn
    @4
    @8
    @1
    c0
    c1o
    cop
    #
    @4
    @8
    c1o
    c1o
    csn
    #
    cxp
    #
    cun
    #
    @8
    @1
    @8
    @12
    ssun1
    @4
    cA
    cvv
    wcel
    #
    @5
    @1
    @13
    wceq
    cA
    @1
    cen
    relen
    brrelexi
    #
    1on
    cA
    c1o
    cvv
    con0
    cdaval
    sylancl
    #
    syl5sseqr
    @4
    @10
    @13
    @1
    @10
    @12
    wcel
    #
    @10
    @13
    wcel
    @4
    c0
    c1o
    wcel
    c1o
    @11
    wcel
    @17
    0lt1o
    c1o
    c1o
    con0
    1on
    elexi
    snid
    c0
    c1o
    c1o
    @11
    opelxpi
    mp2an
    @10
    @12
    @8
    elun2
    mp1i
    @16
    eleqtrrd
    c1o
    c0
    wne
    @10
    @8
    wcel
    #
    wn
    @4
    1n0
    @18
    c1o
    c0
    @18
    c1o
    @7
    wcel
    c1o
    c0
    wceq
    c0
    c1o
    cA
    @7
    opelxp2
    c1o
    c0
    elsni
    syl
    necon3ai
    mp1i
    ssnelpssd
    @8
    cA
    cen
    wbr
    #
    @4
    @9
    @4
    @14
    c0
    cvv
    wcel
    @19
    @15
    0ex
    cA
    c0
    cvv
    cvv
    xpsneng
    sylancl
    @8
    cA
    @1
    entr
    mpancom
    @1
    @8
    fin4i
    syl2anc
    cA
    @1
    fin4en1
    mtod
    con2i
    cA
    @1
    brsdom
    sylanbrc
    @2
    @0
    com
    cA
    cdom
    wbr
    #
    wn
    #
    @2
    @4
    @20
    cA
    @1
    sdomnen
    @20
    @1
    cA
    cA
    infcda1
    ensymd
    nsyl
    @2
    @14
    @0
    @21
    wb
    cA
    @1
    csdm
    relsdom
    brrelexi
    cA
    cvv
    isfin4-2
    syl
    mpbird
    impbii
end
