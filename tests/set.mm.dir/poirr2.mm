include "wpo.mm"
include "cid.mm"
include "cres.mm"
include "cin.mm"
include "c0.mm"
include "wss.mm"
include "wceq.mm"
include "wrel.mm"
include "relres.mm"
include "relin2.mm"
include "mp1i.mm"
include "cv.mm"
include "cop.mm"
include "wcel.mm"
include "wbr.mm"
include "wa.mm"
include "df-br.mm"
include "brin.mm"
include "bitr3i.mm"
include "wn.mm"
include "wi.mm"
include "vex.mm"
include "brres.mm"
include "poirr.mm"
include "wb.mm"
include "ideq.mm"
include "breq2.mm"
include "sylbi.mm"
include "notbid.mm"
include "syl5ibcom.mm"
include "expimpd.mm"
include "ancomsd.mm"
include "syl5bi.mm"
include "con2d.mm"
include "imnan.mm"
include "sylib.mm"
include "pm2.21d.mm"
include "relssdv.mm"
include "ss0.mm"
include "syl.mm"

theorem poirr2
  let cA: class A
  let cR: class R
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cS: class S
  let cV: class V
  let cW: class W


  assert |- ( R Po A -> ( R i^i ( _I |` A ) ) = (/) )

  proof
    cA
    cR
    wpo
    #
    cR
    cid
    cA
    cres
    #
    cin
    #
    c0
    wss
    @2
    c0
    wceq
    @0
    vx
    vy
    @2
    c0
    @1
    wrel
    @2
    wrel
    @0
    cid
    cA
    relres
    cR
    @1
    relin2
    mp1i
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    @2
    wcel
    #
    @3
    @4
    cR
    wbr
    #
    @3
    @4
    @1
    wbr
    #
    wa
    #
    @0
    @5
    c0
    wcel
    #
    @6
    @3
    @4
    @2
    wbr
    @9
    @3
    @4
    @2
    df-br
    @3
    @4
    cR
    @1
    brin
    bitr3i
    @0
    @9
    @10
    @0
    @7
    @8
    wn
    wi
    @9
    wn
    @0
    @8
    @7
    @8
    @3
    @4
    cid
    wbr
    #
    @3
    cA
    wcel
    #
    wa
    @0
    @7
    wn
    #
    @3
    @4
    cid
    cA
    vy
    vex
    #
    brres
    @0
    @12
    @11
    @13
    @0
    @12
    @11
    @13
    @0
    @12
    wa
    @3
    @3
    cR
    wbr
    #
    wn
    @11
    @13
    cA
    @3
    cR
    poirr
    @11
    @15
    @7
    @11
    @3
    @4
    wceq
    @15
    @7
    wb
    @3
    @4
    @14
    ideq
    @3
    @4
    @3
    cR
    breq2
    sylbi
    notbid
    syl5ibcom
    expimpd
    ancomsd
    syl5bi
    con2d
    @7
    @8
    imnan
    sylib
    pm2.21d
    syl5bi
    relssdv
    @2
    ss0
    syl
end
