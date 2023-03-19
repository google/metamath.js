include "csn.mm"
include "cun.mm"
include "cpw.mm"
include "cdif.mm"
include "wcel.mm"
include "wn.mm"
include "wa.mm"
include "eldif.mm"
include "cv.mm"
include "wrex.mm"
include "wral.mm"
include "wss.mm"
include "elpwg.mm"
include "dfss3.mm"
include "syl6bb.mm"
include "notbid.mm"
include "biimpa.mm"
include "rexnal.mm"
include "sylibr.mm"
include "wi.mm"
include "wceq.mm"
include "elpwi.mm"
include "ssel.mm"
include "wo.mm"
include "elun.mm"
include "elsni.mm"
include "orim2i.mm"
include "ord.mm"
include "sylbi.mm"
include "imim2i.mm"
include "impd.mm"
include "3syl.mm"
include "eleq1.mm"
include "biimpd.mm"
include "syl6.mm"
include "expd.mm"
include "com4r.mm"
include "pm2.43b.mm"
include "rexlimdv.mm"
include "imp.mm"
include "syldan.mm"

theorem elpwunsn
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x


  assert |- ( A e. ( ~P ( B u. { C } ) \ ~P B ) -> C e. A )

  proof
    cA
    cB
    cC
    csn
    #
    cun
    #
    cpw
    #
    cB
    cpw
    #
    cdif
    wcel
    cA
    @2
    wcel
    #
    cA
    @3
    wcel
    #
    wn
    #
    wa
    #
    cC
    cA
    wcel
    #
    cA
    @2
    @3
    eldif
    @4
    @6
    vx
    cv
    #
    cB
    wcel
    #
    wn
    #
    vx
    cA
    wrex
    #
    @8
    @7
    @10
    vx
    cA
    wral
    #
    wn
    #
    @12
    @4
    @6
    @14
    @4
    @5
    @13
    @4
    @5
    cA
    cB
    wss
    @13
    cA
    cB
    @2
    elpwg
    vx
    cA
    cB
    dfss3
    syl6bb
    notbid
    biimpa
    @10
    vx
    cA
    rexnal
    sylibr
    @4
    @12
    @8
    @4
    @11
    @8
    vx
    cA
    @4
    @9
    cA
    wcel
    #
    @11
    @8
    wi
    @4
    @15
    @11
    @15
    @8
    @4
    @15
    @11
    @15
    @8
    wi
    #
    @4
    @15
    @11
    wa
    #
    @9
    cC
    wceq
    #
    @16
    @4
    cA
    @1
    wss
    @15
    @9
    @1
    wcel
    #
    wi
    #
    @17
    @18
    wi
    cA
    @1
    elpwi
    cA
    @1
    @9
    ssel
    @20
    @15
    @11
    @18
    @19
    @11
    @18
    wi
    #
    @15
    @19
    @10
    @9
    @0
    wcel
    #
    wo
    #
    @21
    @9
    cB
    @0
    elun
    @23
    @10
    @18
    @22
    @18
    @10
    @9
    cC
    elsni
    orim2i
    ord
    sylbi
    imim2i
    impd
    3syl
    @18
    @15
    @8
    @9
    cC
    cA
    eleq1
    biimpd
    syl6
    expd
    com4r
    pm2.43b
    rexlimdv
    imp
    syldan
    sylbi
end
