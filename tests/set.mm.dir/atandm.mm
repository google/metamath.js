include "cc.mm"
include "ci.mm"
include "cneg.mm"
include "cpr.mm"
include "cdif.mm"
include "wcel.mm"
include "wne.mm"
include "wa.mm"
include "catan.mm"
include "cdm.mm"
include "w3a.mm"
include "wn.mm"
include "eldif.mm"
include "wceq.mm"
include "wo.mm"
include "elprg.mm"
include "notbid.mm"
include "neanior.mm"
include "syl6bbr.mm"
include "pm5.32i.mm"
include "bitri.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "c1.mm"
include "cv.mm"
include "cmul.mm"
include "cmin.mm"
include "clog.mm"
include "cfv.mm"
include "caddc.mm"
include "ovex.mm"
include "df-atan.mm"
include "dmmpti.mm"
include "eleq2i.mm"
include "3anass.mm"
include "3bitr4i.mm"

theorem atandm
  let cA: class A
  let vx: setvar x


  assert |- ( A e. dom arctan <-> ( A e. CC /\ A =/= -u _i /\ A =/= _i ) )

  proof
    cA
    cc
    ci
    cneg
    #
    ci
    cpr
    #
    cdif
    #
    wcel
    #
    cA
    cc
    wcel
    #
    cA
    @0
    wne
    #
    cA
    ci
    wne
    #
    wa
    #
    wa
    #
    cA
    catan
    cdm
    #
    wcel
    @4
    @5
    @6
    w3a
    @3
    @4
    cA
    @1
    wcel
    #
    wn
    #
    wa
    @8
    cA
    cc
    @1
    eldif
    @4
    @11
    @7
    @4
    @11
    cA
    @0
    wceq
    cA
    ci
    wceq
    wo
    #
    wn
    @7
    @4
    @10
    @12
    cA
    @0
    ci
    cc
    elprg
    notbid
    cA
    @0
    cA
    ci
    neanior
    syl6bbr
    pm5.32i
    bitri
    @9
    @2
    cA
    vx
    @2
    ci
    c2
    cdiv
    co
    #
    c1
    ci
    vx
    cv
    cmul
    co
    #
    cmin
    co
    clog
    cfv
    c1
    @14
    caddc
    co
    clog
    cfv
    cmin
    co
    #
    cmul
    co
    catan
    @13
    @15
    cmul
    ovex
    vx
    df-atan
    dmmpti
    eleq2i
    @4
    @5
    @6
    3anass
    3bitr4i
end
