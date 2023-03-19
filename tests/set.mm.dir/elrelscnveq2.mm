include "crels.mm"
include "wcel.mm"
include "ccnv.mm"
include "wss.mm"
include "wa.mm"
include "cv.mm"
include "wbr.mm"
include "wi.mm"
include "wal.mm"
include "wceq.mm"
include "wb.mm"
include "cnvsym.mm"
include "a1i.mm"
include "wrel.mm"
include "elrelsrelim.mm"
include "dfrel2.mm"
include "sylib.mm"
include "sseq1d.mm"
include "syl5rbbr.mm"
include "relbrcnvg.mm"
include "syl.mm"
include "imbi12d.mm"
include "2albidv.mm"
include "bitrd.mm"
include "anbi12d.mm"
include "eqss.mm"
include "2albiim.mm"
include "3bitr4g.mm"

theorem elrelscnveq2
  let vx: setvar x
  let vy: setvar y
  let cR: class R

  disjoint R x
  disjoint R y
  disjoint x y
  assert |- ( R e. Rels -> ( `' R = R <-> A. x A. y ( x R y <-> y R x ) ) )

  proof
    cR
    crels
    wcel
    #
    cR
    ccnv
    #
    cR
    wss
    #
    cR
    @1
    wss
    #
    wa
    vx
    cv
    #
    vy
    cv
    #
    cR
    wbr
    #
    @5
    @4
    cR
    wbr
    #
    wi
    vy
    wal
    vx
    wal
    #
    @7
    @6
    wi
    #
    vy
    wal
    vx
    wal
    #
    wa
    @1
    cR
    wceq
    @6
    @7
    wb
    vy
    wal
    vx
    wal
    @0
    @2
    @8
    @3
    @10
    @2
    @8
    wb
    @0
    vx
    vy
    cR
    cnvsym
    a1i
    @0
    @3
    @4
    @5
    @1
    wbr
    #
    @5
    @4
    @1
    wbr
    #
    wi
    #
    vy
    wal
    vx
    wal
    #
    @10
    @14
    @1
    ccnv
    #
    @1
    wss
    @0
    @3
    vx
    vy
    @1
    cnvsym
    @0
    @15
    cR
    @1
    @0
    cR
    wrel
    #
    @15
    cR
    wceq
    cR
    elrelsrelim
    #
    cR
    dfrel2
    sylib
    sseq1d
    syl5rbbr
    @0
    @13
    @9
    vx
    vy
    @0
    @11
    @7
    @12
    @6
    @0
    @16
    @11
    @7
    wb
    @17
    @4
    @5
    cR
    relbrcnvg
    syl
    @0
    @16
    @12
    @6
    wb
    @17
    @5
    @4
    cR
    relbrcnvg
    syl
    imbi12d
    2albidv
    bitrd
    anbi12d
    @1
    cR
    eqss
    @6
    @7
    vx
    vy
    2albiim
    3bitr4g
end
