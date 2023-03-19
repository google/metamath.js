include "cnp.mm"
include "wcel.mm"
include "wa.mm"
include "cltq.mm"
include "wbr.mm"
include "wi.mm"
include "cvv.mm"
include "cnq.mm"
include "cxp.mm"
include "wss.mm"
include "wrel.mm"
include "ltrelnq.mm"
include "relxp.mm"
include "relss.mm"
include "mp2.mm"
include "brrelexi.mm"
include "cv.mm"
include "wceq.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "breq2.mm"
include "anbi12d.mm"
include "imbi1d.mm"
include "breq1.mm"
include "imbi12d.mm"
include "wal.mm"
include "wrex.mm"
include "c0.mm"
include "wpss.mm"
include "w3a.mm"
include "wral.mm"
include "elnpi.mm"
include "simprbi.mm"
include "r19.21bi.mm"
include "simpld.mm"
include "19.21bi.mm"
include "imp.mm"
include "vtocl2g.mm"
include "sylan2.mm"
include "adantll.mm"
include "pm2.43i.mm"
include "ex.mm"

theorem prcdnq
  let cA: class A
  let cB: class B
  let cC: class C
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. P. /\ B e. A ) -> ( C <Q B -> C e. A ) )

  proof
    cA
    cnp
    wcel
    #
    cB
    cA
    wcel
    #
    wa
    #
    cC
    cB
    cltq
    wbr
    #
    cC
    cA
    wcel
    #
    @2
    @3
    wa
    #
    @4
    @1
    @3
    @5
    @4
    wi
    #
    @0
    @3
    @1
    cC
    cvv
    wcel
    @6
    cC
    cB
    cltq
    cltq
    cnq
    cnq
    cxp
    #
    wss
    @7
    wrel
    cltq
    wrel
    ltrelnq
    cnq
    cnq
    relxp
    cltq
    @7
    relss
    mp2
    brrelexi
    @0
    vx
    cv
    #
    cA
    wcel
    #
    wa
    #
    vy
    cv
    #
    @8
    cltq
    wbr
    #
    wa
    #
    @11
    cA
    wcel
    #
    wi
    @2
    @11
    cB
    cltq
    wbr
    #
    wa
    #
    @14
    wi
    @6
    vx
    vy
    cB
    cC
    cA
    cvv
    @8
    cB
    wceq
    #
    @13
    @16
    @14
    @17
    @10
    @2
    @12
    @15
    @17
    @9
    @1
    @0
    @8
    cB
    cA
    eleq1
    anbi2d
    @8
    cB
    @11
    cltq
    breq2
    anbi12d
    imbi1d
    @11
    cC
    wceq
    #
    @16
    @5
    @14
    @4
    @18
    @15
    @3
    @2
    @11
    cC
    cB
    cltq
    breq1
    anbi2d
    @11
    cC
    cA
    eleq1
    imbi12d
    @10
    @12
    @14
    @10
    @12
    @14
    wi
    #
    vy
    @10
    @19
    vy
    wal
    #
    @8
    @11
    cltq
    wbr
    vy
    cA
    wrex
    #
    @0
    @20
    @21
    wa
    #
    vx
    cA
    @0
    cA
    cvv
    wcel
    c0
    cA
    wpss
    cA
    cnq
    wpss
    w3a
    @22
    vx
    cA
    wral
    vx
    vy
    cA
    elnpi
    simprbi
    r19.21bi
    simpld
    19.21bi
    imp
    vtocl2g
    sylan2
    adantll
    pm2.43i
    ex
end
