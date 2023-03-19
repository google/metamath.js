include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "ccda.mm"
include "co.mm"
include "cen.mm"
include "wbr.mm"
include "c1o.mm"
include "csn.mm"
include "cxp.mm"
include "c0.mm"
include "cun.mm"
include "con0.mm"
include "1on.mm"
include "xpsneng.mm"
include "mpan2.mm"
include "0ex.mm"
include "ensym.mm"
include "cin.mm"
include "wceq.mm"
include "incom.mm"
include "xp01disj.mm"
include "eqtri.mm"
include "cdaenun.mm"
include "mp3an3.mm"
include "syl2an.mm"
include "cdaval.mm"
include "ancoms.mm"
include "uncom.mm"
include "syl6eq.mm"
include "breqtrrd.mm"
include "wn.mm"
include "enref.mm"
include "a1i.mm"
include "wfn.mm"
include "cdm.mm"
include "cdafn.mm"
include "fndm.mm"
include "ax-mp.mm"
include "ndmov.mm"
include "ancom.mm"
include "sylnbi.mm"
include "3brtr4d.mm"
include "pm2.61i.mm"

theorem cdacomen
  let cA: class A
  let cB: class B


  assert |- ( A +c B ) ~~ ( B +c A )

  proof
    cA
    cvv
    wcel
    #
    cB
    cvv
    wcel
    #
    wa
    #
    cA
    cB
    ccda
    co
    #
    cB
    cA
    ccda
    co
    #
    cen
    wbr
    @2
    @3
    cA
    c1o
    csn
    cxp
    #
    cB
    c0
    csn
    cxp
    #
    cun
    #
    @4
    cen
    @0
    @5
    cA
    cen
    wbr
    #
    @6
    cB
    cen
    wbr
    #
    @3
    @7
    cen
    wbr
    #
    @1
    @0
    c1o
    con0
    wcel
    @8
    1on
    cA
    c1o
    cvv
    con0
    xpsneng
    mpan2
    @1
    c0
    cvv
    wcel
    @9
    0ex
    cB
    c0
    cvv
    cvv
    xpsneng
    mpan2
    @8
    cA
    @5
    cen
    wbr
    #
    cB
    @6
    cen
    wbr
    #
    @10
    @9
    @5
    cA
    ensym
    @6
    cB
    ensym
    @11
    @12
    @5
    @6
    cin
    #
    c0
    wceq
    @10
    @13
    @6
    @5
    cin
    c0
    @5
    @6
    incom
    cB
    cA
    xp01disj
    eqtri
    cA
    @5
    cB
    @6
    cdaenun
    mp3an3
    syl2an
    syl2an
    @2
    @4
    @6
    @5
    cun
    #
    @7
    @1
    @0
    @4
    @14
    wceq
    cB
    cA
    cvv
    cvv
    cdaval
    ancoms
    @6
    @5
    uncom
    syl6eq
    breqtrrd
    @2
    wn
    #
    c0
    c0
    @3
    @4
    cen
    c0
    c0
    cen
    wbr
    @15
    c0
    0ex
    enref
    a1i
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
    @16
    wceq
    cdafn
    @16
    ccda
    fndm
    ax-mp
    #
    ndmov
    @2
    @1
    @0
    wa
    @4
    c0
    wceq
    @0
    @1
    ancom
    cB
    cA
    cvv
    ccda
    @17
    ndmov
    sylnbi
    3brtr4d
    pm2.61i
end
