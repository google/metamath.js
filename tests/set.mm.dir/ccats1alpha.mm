include "cword.mm"
include "wcel.mm"
include "wa.mm"
include "cs1.mm"
include "cconcat.mm"
include "co.mm"
include "cvv.mm"
include "wb.mm"
include "wrdv.mm"
include "s1cli.mm"
include "a1i.mm"
include "ccatalpha.mm"
include "syl2an.mm"
include "cv.mm"
include "wceq.mm"
include "wrex.mm"
include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "simpr.mm"
include "s1len.mm"
include "wrdl1exs1.mm"
include "sylancl.mm"
include "elex.mm"
include "adantr.mm"
include "s111.mm"
include "eleq1.mm"
include "syl5ibrcom.mm"
include "sylbid.mm"
include "rexlimdva.mm"
include "mpd.mm"
include "ex.mm"
include "s1cl.mm"
include "impbid1.mm"
include "anbi2d.mm"
include "adantl.mm"
include "bitrd.mm"

theorem ccats1alpha
  let cA: class A
  let cS: class S
  let cU: class U
  let cV: class V
  let cX: class X
  let vw: setvar w


  assert |- ( ( A e. Word V /\ X e. U ) -> ( ( A ++ <" X "> ) e. Word S <-> ( A e. Word S /\ X e. S ) ) )

  proof
    cA
    cV
    cword
    wcel
    #
    cX
    cU
    wcel
    #
    wa
    cA
    cX
    cs1
    #
    cconcat
    co
    cS
    cword
    #
    wcel
    #
    cA
    @3
    wcel
    #
    @2
    @3
    wcel
    #
    wa
    #
    @5
    cX
    cS
    wcel
    #
    wa
    #
    @0
    cA
    cvv
    cword
    #
    wcel
    @2
    @10
    wcel
    #
    @4
    @7
    wb
    @1
    cV
    cA
    wrdv
    @11
    @1
    cX
    s1cli
    a1i
    cA
    @2
    cS
    ccatalpha
    syl2an
    @1
    @7
    @9
    wb
    @0
    @1
    @6
    @8
    @5
    @1
    @6
    @8
    @1
    @6
    @8
    @1
    @6
    wa
    #
    @2
    vw
    cv
    #
    cs1
    wceq
    #
    vw
    cS
    wrex
    #
    @8
    @12
    @6
    @2
    chash
    cfv
    c1
    wceq
    @15
    @1
    @6
    simpr
    cX
    s1len
    cS
    @2
    vw
    wrdl1exs1
    sylancl
    @12
    @14
    @8
    vw
    cS
    @12
    @13
    cS
    wcel
    #
    wa
    #
    @14
    cX
    @13
    wceq
    #
    @8
    @12
    cX
    cvv
    wcel
    #
    @13
    cvv
    wcel
    @14
    @18
    wb
    @16
    @1
    @19
    @6
    cX
    cU
    elex
    adantr
    @13
    cS
    elex
    cvv
    cX
    @13
    s111
    syl2an
    @17
    @8
    @18
    @16
    @12
    @16
    simpr
    cX
    @13
    cS
    eleq1
    syl5ibrcom
    sylbid
    rexlimdva
    mpd
    ex
    cX
    cS
    s1cl
    impbid1
    anbi2d
    adantl
    bitrd
end
