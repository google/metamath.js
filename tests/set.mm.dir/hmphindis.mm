include "c0.mm"
include "cpr.mm"
include "chmph.mm"
include "wbr.mm"
include "wceq.mm"
include "cid.mm"
include "cfv.mm"
include "wa.mm"
include "csn.mm"
include "dfsn2.mm"
include "indislem.mm"
include "preq2.mm"
include "syl6eqr.mm"
include "syl5eqr.mm"
include "breq2d.mm"
include "biimpac.mm"
include "hmph0.mm"
include "sylib.mm"
include "cuni.mm"
include "unieqd.mm"
include "0ex.mm"
include "unisn.mm"
include "eqcomi.mm"
include "3eqtr4g.mm"
include "preq2d.mm"
include "3eqtr4a.mm"
include "wne.mm"
include "c2o.mm"
include "cen.mm"
include "hmphen.mm"
include "adantr.mm"
include "necom.mm"
include "cvv.mm"
include "wcel.mm"
include "fvex.mm"
include "pr2nelem.mm"
include "mp3an12.mm"
include "sylbi.mm"
include "adantl.mm"
include "syl5eqbrr.mm"
include "entr.mm"
include "syl2anc.mm"
include "ctopon.mm"
include "wb.mm"
include "ctop.mm"
include "hmphtop1.mm"
include "toptopon.mm"
include "en2top.mm"
include "syl.mm"
include "mpbid.mm"
include "simpld.mm"
include "pm2.61dane.mm"

theorem hmphindis
  let cA: class A
  let cJ: class J
  let cX: class X
  let vf: setvar f
  let vx: setvar x
  assume hmphdis.1: |- X = U. J


  assert |- ( J ~= { (/) , A } -> J = { (/) , X } )

  proof
    cJ
    c0
    cA
    cpr
    #
    chmph
    wbr
    #
    cJ
    c0
    cX
    cpr
    #
    wceq
    #
    cA
    cid
    cfv
    #
    c0
    @1
    @4
    c0
    wceq
    #
    wa
    #
    c0
    csn
    #
    c0
    c0
    cpr
    #
    cJ
    @2
    c0
    dfsn2
    #
    @6
    cJ
    @7
    chmph
    wbr
    #
    cJ
    @7
    wceq
    @5
    @1
    @10
    @5
    @0
    @7
    cJ
    chmph
    @5
    @0
    c0
    @4
    cpr
    #
    @7
    cA
    indislem
    #
    @5
    @11
    @8
    @7
    @4
    c0
    c0
    preq2
    @9
    syl6eqr
    syl5eqr
    breq2d
    biimpac
    cJ
    hmph0
    sylib
    #
    @6
    cX
    c0
    c0
    @6
    cJ
    cuni
    @7
    cuni
    #
    cX
    c0
    @6
    cJ
    @7
    @13
    unieqd
    hmphdis.1
    @14
    c0
    c0
    0ex
    unisn
    eqcomi
    3eqtr4g
    preq2d
    3eqtr4a
    @1
    @4
    c0
    wne
    #
    wa
    #
    @3
    cX
    c0
    wne
    #
    @16
    cJ
    c2o
    cen
    wbr
    #
    @3
    @17
    wa
    #
    @16
    cJ
    @0
    cen
    wbr
    #
    @0
    c2o
    cen
    wbr
    @18
    @1
    @20
    @15
    cJ
    @0
    hmphen
    adantr
    @16
    @0
    @11
    c2o
    cen
    @12
    @15
    @11
    c2o
    cen
    wbr
    #
    @1
    @15
    c0
    @4
    wne
    #
    @21
    @4
    c0
    necom
    c0
    cvv
    wcel
    @4
    cvv
    wcel
    @22
    @21
    0ex
    cA
    cid
    fvex
    c0
    @4
    cvv
    cvv
    pr2nelem
    mp3an12
    sylbi
    adantl
    syl5eqbrr
    cJ
    @0
    c2o
    entr
    syl2anc
    @16
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    @18
    @19
    wb
    @16
    cJ
    ctop
    wcel
    #
    @23
    @1
    @24
    @15
    cJ
    @0
    hmphtop1
    adantr
    cJ
    cX
    hmphdis.1
    toptopon
    sylib
    cJ
    cX
    en2top
    syl
    mpbid
    simpld
    pm2.61dane
end
