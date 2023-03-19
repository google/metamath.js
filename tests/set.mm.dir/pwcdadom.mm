include "ccda.mm"
include "co.mm"
include "cpw.mm"
include "cdom.mm"
include "wbr.mm"
include "c1o.mm"
include "csn.mm"
include "cxp.mm"
include "cen.mm"
include "c0.mm"
include "cwdom.mm"
include "wn.mm"
include "canthwdom.mm"
include "wi.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "0elpw.mm"
include "n0ii.mm"
include "dom0.mm"
include "mtbir.mm"
include "wfn.mm"
include "cdm.mm"
include "cdafn.mm"
include "fndm.mm"
include "ax-mp.mm"
include "ndmov.mm"
include "breq2d.mm"
include "mtbiri.mm"
include "con4i.mm"
include "simpld.mm"
include "0ex.mm"
include "xpsneng.mm"
include "sylancl.mm"
include "endom.mm"
include "domwdom.mm"
include "wdomtr.mm"
include "expcom.mm"
include "4syl.mm"
include "mtoi.mm"
include "cun.mm"
include "wo.mm"
include "wb.mm"
include "pwcdaen.mm"
include "syl2anc.mm"
include "domen1.mm"
include "syl.mm"
include "ibi.mm"
include "cdaval.mm"
include "breqtrd.mm"
include "unxpwdom.mm"
include "ord.mm"
include "mpd.mm"
include "con0.mm"
include "simprd.mm"
include "1on.mm"
include "domentr.mm"

theorem pwcdadom
  let cA: class A
  let cB: class B


  assert |- ( ~P ( A +c A ) ~<_ ( A +c B ) -> ~P A ~<_ B )

  proof
    cA
    cA
    ccda
    co
    #
    cpw
    #
    cA
    cB
    ccda
    co
    #
    cdom
    wbr
    #
    cA
    cpw
    #
    cB
    c1o
    csn
    cxp
    #
    cdom
    wbr
    #
    @5
    cB
    cen
    wbr
    #
    @4
    cB
    cdom
    wbr
    @3
    @4
    cA
    c0
    csn
    cxp
    #
    cwdom
    wbr
    #
    wn
    @6
    @3
    @9
    @4
    cA
    cwdom
    wbr
    #
    cA
    canthwdom
    @3
    @8
    cA
    cen
    wbr
    #
    @8
    cA
    cdom
    wbr
    @8
    cA
    cwdom
    wbr
    #
    @9
    @10
    wi
    @3
    cA
    cvv
    wcel
    #
    c0
    cvv
    wcel
    @11
    @3
    @13
    cB
    cvv
    wcel
    #
    @13
    @14
    wa
    #
    @3
    @15
    wn
    #
    @3
    @1
    c0
    cdom
    wbr
    #
    @17
    @1
    c0
    wceq
    c0
    @1
    @0
    0elpw
    n0ii
    @1
    dom0
    mtbir
    @16
    @2
    c0
    @1
    cdom
    cA
    cB
    cvv
    ccda
    ccda
    cvv
    cvv
    cxp
    #
    wfn
    ccda
    cdm
    @18
    wceq
    cdafn
    @18
    ccda
    fndm
    ax-mp
    ndmov
    breq2d
    mtbiri
    con4i
    #
    simpld
    #
    0ex
    cA
    c0
    cvv
    cvv
    xpsneng
    sylancl
    @8
    cA
    endom
    @8
    cA
    domwdom
    @9
    @12
    @10
    @4
    @8
    cA
    wdomtr
    expcom
    4syl
    mtoi
    @3
    @9
    @6
    @3
    @4
    @4
    cxp
    #
    @8
    @5
    cun
    #
    cdom
    wbr
    @9
    @6
    wo
    @3
    @21
    @2
    @22
    cdom
    @3
    @21
    @2
    cdom
    wbr
    #
    @3
    @1
    @21
    cen
    wbr
    #
    @3
    @23
    wb
    @3
    @13
    @13
    @24
    @20
    @20
    cA
    cA
    cvv
    cvv
    pwcdaen
    syl2anc
    @1
    @21
    @2
    domen1
    syl
    ibi
    @3
    @15
    @2
    @22
    wceq
    @19
    cA
    cB
    cvv
    cvv
    cdaval
    syl
    breqtrd
    @4
    @8
    @5
    unxpwdom
    syl
    ord
    mpd
    @3
    @14
    c1o
    con0
    wcel
    @7
    @3
    @13
    @14
    @19
    simprd
    1on
    cB
    c1o
    cvv
    con0
    xpsneng
    sylancl
    @4
    @5
    cB
    domentr
    syl2anc
end
