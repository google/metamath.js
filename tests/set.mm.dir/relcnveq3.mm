include "ccnv.mm"
include "wceq.mm"
include "wss.mm"
include "wa.mm"
include "wrel.mm"
include "cv.mm"
include "wbr.mm"
include "wi.mm"
include "wal.mm"
include "eqss.mm"
include "cnvsym.mm"
include "biimpi.mm"
include "a1d.mm"
include "adantl.mm"
include "com12.mm"
include "dfrel2.mm"
include "cnvss.mm"
include "sseq1.mm"
include "syl5ibcom.mm"
include "sylbir.mm"
include "sylbi.mm"
include "biimpri.mm"
include "jca2.mm"
include "impbid.mm"
include "syl5bb.mm"

theorem relcnveq3
  let vx: setvar x
  let vy: setvar y
  let cR: class R

  disjoint R x
  disjoint R y
  disjoint x y
  assert |- ( Rel R -> ( R = `' R <-> A. x A. y ( x R y -> y R x ) ) )

  proof
    cR
    cR
    ccnv
    #
    wceq
    cR
    @0
    wss
    #
    @0
    cR
    wss
    #
    wa
    #
    cR
    wrel
    #
    vx
    cv
    #
    vy
    cv
    #
    cR
    wbr
    @6
    @5
    cR
    wbr
    wi
    vy
    wal
    vx
    wal
    #
    cR
    @0
    eqss
    @4
    @3
    @7
    @3
    @4
    @7
    @2
    @4
    @7
    wi
    @1
    @2
    @7
    @4
    @2
    @7
    vx
    vy
    cR
    cnvsym
    #
    biimpi
    a1d
    adantl
    com12
    @4
    @7
    @1
    @2
    @4
    @0
    ccnv
    #
    cR
    wceq
    #
    @7
    @1
    wi
    cR
    dfrel2
    @7
    @10
    @1
    @7
    @2
    @10
    @1
    wi
    @8
    @2
    @9
    @0
    wss
    @10
    @1
    @0
    cR
    cnvss
    @9
    cR
    @0
    sseq1
    syl5ibcom
    sylbir
    com12
    sylbi
    @2
    @7
    @8
    biimpri
    jca2
    impbid
    syl5bb
end
