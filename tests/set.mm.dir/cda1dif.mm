include "c1o.mm"
include "ccda.mm"
include "co.mm"
include "wcel.mm"
include "csn.mm"
include "cdif.mm"
include "c0.mm"
include "cop.mm"
include "cen.mm"
include "wbr.mm"
include "cvv.mm"
include "ovexd.mm"
include "id.mm"
include "cxp.mm"
include "cun.mm"
include "wss.mm"
include "df1o2.mm"
include "xpeq1i.mm"
include "0ex.mm"
include "con0.mm"
include "1on.mm"
include "elexi.mm"
include "xpsn.mm"
include "eqtri.mm"
include "ssun2.mm"
include "eqsstr3i.mm"
include "opex.mm"
include "snss.mm"
include "mpbir.mm"
include "wceq.mm"
include "cdm.mm"
include "wrel.mm"
include "relxp.mm"
include "wfn.mm"
include "cdafn.mm"
include "fndm.mm"
include "ax-mp.mm"
include "releqi.mm"
include "ovrcl.mm"
include "simpld.mm"
include "cdaval.mm"
include "sylancl.mm"
include "syl5eleqr.mm"
include "difsnen.mm"
include "syl3anc.mm"
include "difeq1d.mm"
include "cin.mm"
include "xp01disj.mm"
include "disj3.mm"
include "mpbi.mm"
include "difun2.mm"
include "difeq2i.mm"
include "3eqtr2i.mm"
include "syl6eqr.mm"
include "xpsneng.mm"
include "eqbrtrd.mm"
include "entr.mm"
include "syl2anc.mm"

theorem cda1dif
  let cA: class A
  let cB: class B


  assert |- ( B e. ( A +c 1o ) -> ( ( A +c 1o ) \ { B } ) ~~ A )

  proof
    cB
    cA
    c1o
    ccda
    co
    #
    wcel
    #
    @0
    cB
    csn
    cdif
    #
    @0
    c0
    c1o
    cop
    #
    csn
    #
    cdif
    #
    cen
    wbr
    #
    @5
    cA
    cen
    wbr
    @2
    cA
    cen
    wbr
    @1
    @0
    cvv
    wcel
    @1
    @3
    @0
    wcel
    @6
    @1
    cA
    c1o
    ccda
    ovexd
    @1
    id
    @1
    @3
    cA
    c0
    csn
    #
    cxp
    #
    c1o
    c1o
    csn
    #
    cxp
    #
    cun
    #
    @0
    @3
    @11
    wcel
    @4
    @11
    wss
    @4
    @10
    @11
    @10
    @7
    @9
    cxp
    @4
    c1o
    @7
    @9
    df1o2
    xpeq1i
    c0
    c1o
    0ex
    c1o
    con0
    1on
    elexi
    xpsn
    eqtri
    #
    @10
    @8
    ssun2
    eqsstr3i
    @3
    @11
    c0
    c1o
    opex
    snss
    mpbir
    @1
    cA
    cvv
    wcel
    #
    c1o
    con0
    wcel
    @0
    @11
    wceq
    @1
    @13
    c1o
    cvv
    wcel
    cA
    c1o
    cB
    ccda
    ccda
    cdm
    #
    wrel
    cvv
    cvv
    cxp
    #
    wrel
    cvv
    cvv
    relxp
    @14
    @15
    ccda
    @15
    wfn
    @14
    @15
    wceq
    cdafn
    @15
    ccda
    fndm
    ax-mp
    releqi
    mpbir
    ovrcl
    simpld
    #
    1on
    cA
    c1o
    cvv
    con0
    cdaval
    sylancl
    #
    syl5eleqr
    cB
    @3
    cvv
    @0
    difsnen
    syl3anc
    @1
    @5
    @8
    cA
    cen
    @1
    @5
    @11
    @4
    cdif
    #
    @8
    @1
    @0
    @11
    @4
    @17
    difeq1d
    @8
    @8
    @10
    cdif
    #
    @11
    @10
    cdif
    @18
    @8
    @10
    cin
    c0
    wceq
    @8
    @19
    wceq
    cA
    c1o
    xp01disj
    @8
    @10
    disj3
    mpbi
    @8
    @10
    difun2
    @10
    @4
    @11
    @12
    difeq2i
    3eqtr2i
    syl6eqr
    @1
    @13
    c0
    cvv
    wcel
    @8
    cA
    cen
    wbr
    @16
    0ex
    cA
    c0
    cvv
    cvv
    xpsneng
    sylancl
    eqbrtrd
    @2
    @5
    cA
    entr
    syl2anc
end
