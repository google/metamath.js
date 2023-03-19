include "cid.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "cv.mm"
include "cop.mm"
include "wcel.mm"
include "cvv.mm"
include "cdif.mm"
include "wi.mm"
include "wal.mm"
include "wbr.mm"
include "wn.mm"
include "wss.mm"
include "incom.mm"
include "eqeq1i.mm"
include "disj2.mm"
include "wrel.mm"
include "wb.mm"
include "reli.mm"
include "ssrel.mm"
include "ax-mp.mm"
include "3bitri.mm"
include "equcom.mm"
include "vex.mm"
include "ideq.mm"
include "df-br.mm"
include "3bitr2i.mm"
include "wa.mm"
include "opex.mm"
include "biantrur.mm"
include "eldif.mm"
include "bitr4i.mm"
include "xchnxbir.mm"
include "imbi12i.mm"
include "2albii.mm"
include "breq2.mm"
include "notbid.mm"
include "equsalvw.mm"
include "albii.mm"

theorem intirr
  let vx: setvar x
  let cR: class R
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cS: class S
  let cV: class V
  let cW: class W

  disjoint R x
  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint R y
  disjoint R z
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint V z
  disjoint W z
  assert |- ( ( R i^i _I ) = (/) <-> A. x -. x R x )

  proof
    cR
    cid
    cin
    #
    c0
    wceq
    #
    vx
    cv
    #
    vy
    cv
    #
    cop
    #
    cid
    wcel
    #
    @4
    cvv
    cR
    cdif
    #
    wcel
    #
    wi
    #
    vy
    wal
    vx
    wal
    #
    @3
    @2
    wceq
    #
    @2
    @3
    cR
    wbr
    #
    wn
    #
    wi
    #
    vy
    wal
    #
    vx
    wal
    @2
    @2
    cR
    wbr
    #
    wn
    #
    vx
    wal
    @1
    cid
    cR
    cin
    #
    c0
    wceq
    cid
    @6
    wss
    #
    @9
    @0
    @17
    c0
    cR
    cid
    incom
    eqeq1i
    cid
    cR
    disj2
    cid
    wrel
    @18
    @9
    wb
    reli
    vx
    vy
    cid
    @6
    ssrel
    ax-mp
    3bitri
    @13
    @8
    vx
    vy
    @10
    @5
    @12
    @7
    @10
    @2
    @3
    wceq
    @2
    @3
    cid
    wbr
    @5
    vy
    vx
    equcom
    @2
    @3
    vy
    vex
    ideq
    @2
    @3
    cid
    df-br
    3bitr2i
    @4
    cR
    wcel
    #
    @7
    @11
    @19
    wn
    #
    @4
    cvv
    wcel
    #
    @20
    wa
    @7
    @21
    @20
    @2
    @3
    opex
    biantrur
    @4
    cvv
    cR
    eldif
    bitr4i
    @2
    @3
    cR
    df-br
    xchnxbir
    imbi12i
    2albii
    @14
    @16
    vx
    @12
    @16
    vy
    vx
    @10
    @11
    @15
    @3
    @2
    @2
    cR
    breq2
    notbid
    equsalvw
    albii
    3bitr2i
end
