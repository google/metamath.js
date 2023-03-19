include "wor.mm"
include "wpo.mm"
include "cv.mm"
include "wbr.mm"
include "weq.mm"
include "w3o.mm"
include "wral.mm"
include "wa.mm"
include "cxp.mm"
include "cid.mm"
include "ccnv.mm"
include "cun.mm"
include "wss.mm"
include "df-so.mm"
include "cop.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "opelxp.mm"
include "wo.mm"
include "brun.mm"
include "vex.mm"
include "ideq.mm"
include "brcnv.mm"
include "orbi12i.mm"
include "bitr2i.mm"
include "orbi2i.mm"
include "3orass.mm"
include "3bitr4i.mm"
include "df-br.mm"
include "imbi12i.mm"
include "2albii.mm"
include "wrel.mm"
include "wb.mm"
include "relxp.mm"
include "ssrel.mm"
include "ax-mp.mm"
include "r2al.mm"
include "anbi2i.mm"
include "bitr4i.mm"

theorem dfso2
  let cA: class A
  let cR: class R
  let vx: setvar x
  let vy: setvar y


  assert |- ( R Or A <-> ( R Po A /\ ( A X. A ) C_ ( R u. ( _I u. `' R ) ) ) )

  proof
    cA
    cR
    wor
    cA
    cR
    wpo
    #
    vx
    cv
    #
    vy
    cv
    #
    cR
    wbr
    #
    vx
    vy
    weq
    #
    @2
    @1
    cR
    wbr
    #
    w3o
    #
    vy
    cA
    wral
    vx
    cA
    wral
    #
    wa
    @0
    cA
    cA
    cxp
    #
    cR
    cid
    cR
    ccnv
    #
    cun
    #
    cun
    #
    wss
    #
    wa
    vx
    vy
    cA
    cR
    df-so
    @12
    @7
    @0
    @1
    @2
    cop
    #
    @8
    wcel
    #
    @13
    @11
    wcel
    #
    wi
    #
    vy
    wal
    vx
    wal
    #
    @1
    cA
    wcel
    @2
    cA
    wcel
    wa
    #
    @6
    wi
    #
    vy
    wal
    vx
    wal
    @12
    @7
    @16
    @19
    vx
    vy
    @14
    @18
    @15
    @6
    @1
    @2
    cA
    cA
    opelxp
    @6
    @1
    @2
    @11
    wbr
    #
    @15
    @3
    @4
    @5
    wo
    #
    wo
    @3
    @1
    @2
    @10
    wbr
    #
    wo
    @6
    @20
    @21
    @22
    @3
    @22
    @1
    @2
    cid
    wbr
    #
    @1
    @2
    @9
    wbr
    #
    wo
    @21
    @1
    @2
    cid
    @9
    brun
    @23
    @4
    @24
    @5
    @1
    @2
    vy
    vex
    #
    ideq
    @1
    @2
    cR
    vx
    vex
    @25
    brcnv
    orbi12i
    bitr2i
    orbi2i
    @3
    @4
    @5
    3orass
    @1
    @2
    cR
    @10
    brun
    3bitr4i
    @1
    @2
    @11
    df-br
    bitr2i
    imbi12i
    2albii
    @8
    wrel
    @12
    @17
    wb
    cA
    cA
    relxp
    vx
    vy
    @8
    @11
    ssrel
    ax-mp
    @6
    vx
    vy
    cA
    cA
    r2al
    3bitr4i
    anbi2i
    bitr4i
end
