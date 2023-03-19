include "cvv.mm"
include "cxp.mm"
include "copab.mm"
include "cdif.mm"
include "wn.mm"
include "wceq.mm"
include "cv.mm"
include "cop.mm"
include "wcel.mm"
include "wb.mm"
include "wal.mm"
include "opabid.mm"
include "notbii.mm"
include "opelvvdif.mm"
include "el2v.mm"
include "3bitr4i.mm"
include "gen2.mm"
include "wrel.mm"
include "relxp.mm"
include "reldif.mm"
include "ax-mp.mm"
include "relopab.mm"
include "nfcv.mm"
include "nfopab1.mm"
include "nfdif.mm"
include "nfopab2.mm"
include "eqrelf.mm"
include "mp2an.mm"
include "mpbir.mm"

theorem vvdifopab
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y

  disjoint x y
  assert |- ( ( _V X. _V ) \ { <. x , y >. | ph } ) = { <. x , y >. | -. ph }

  proof
    cvv
    cvv
    cxp
    #
    wph
    vx
    vy
    copab
    #
    cdif
    #
    wph
    wn
    #
    vx
    vy
    copab
    #
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
    @2
    wcel
    #
    @8
    @4
    wcel
    #
    wb
    #
    vy
    wal
    vx
    wal
    #
    @11
    vx
    vy
    @8
    @1
    wcel
    #
    wn
    #
    @3
    @9
    @10
    @13
    wph
    wph
    vx
    vy
    opabid
    notbii
    @9
    @14
    wb
    vx
    vy
    @6
    @7
    @1
    cvv
    cvv
    opelvvdif
    el2v
    @3
    vx
    vy
    opabid
    3bitr4i
    gen2
    @2
    wrel
    #
    @4
    wrel
    @5
    @12
    wb
    @0
    wrel
    @15
    cvv
    cvv
    relxp
    @0
    @1
    reldif
    ax-mp
    @3
    vx
    vy
    relopab
    vx
    vy
    @2
    @4
    vx
    @0
    @1
    vx
    @0
    nfcv
    wph
    vx
    vy
    nfopab1
    nfdif
    @3
    vx
    vy
    nfopab1
    vy
    @0
    @1
    vy
    @0
    nfcv
    wph
    vx
    vy
    nfopab2
    nfdif
    @3
    vx
    vy
    nfopab2
    eqrelf
    mp2an
    mpbir
end
