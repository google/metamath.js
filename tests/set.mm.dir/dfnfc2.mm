include "wcel.mm"
include "wal.mm"
include "wnfc.mm"
include "cv.mm"
include "wceq.mm"
include "wnf.mm"
include "nfcvd.mm"
include "id.mm"
include "nfeqd.mm"
include "alrimiv.mm"
include "csn.mm"
include "cuni.mm"
include "df-nfc.mm"
include "velsn.mm"
include "nfbii.mm"
include "albii.mm"
include "sylbbr.mm"
include "nfunid.mm"
include "nfa1.mm"
include "unisng.mm"
include "sps.mm"
include "nfceqdf.mm"
include "syl5ib.mm"
include "impbid2.mm"

theorem dfnfc2
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cV: class V

  disjoint x y
  disjoint A y
  assert |- ( A. x A e. V -> ( F/_ x A <-> A. y F/ x y = A ) )

  proof
    cA
    cV
    wcel
    #
    vx
    wal
    #
    vx
    cA
    wnfc
    #
    vy
    cv
    #
    cA
    wceq
    #
    vx
    wnf
    #
    vy
    wal
    #
    @2
    @5
    vy
    @2
    vx
    @3
    cA
    @2
    vx
    @3
    nfcvd
    @2
    id
    nfeqd
    alrimiv
    @6
    vx
    cA
    csn
    #
    cuni
    #
    wnfc
    @1
    @2
    @6
    vx
    @7
    vx
    @7
    wnfc
    @3
    @7
    wcel
    #
    vx
    wnf
    #
    vy
    wal
    @6
    vx
    vy
    @7
    df-nfc
    @10
    @5
    vy
    @9
    @4
    vx
    vy
    cA
    velsn
    nfbii
    albii
    sylbbr
    nfunid
    @1
    vx
    @8
    cA
    @0
    vx
    nfa1
    @0
    @8
    cA
    wceq
    vx
    cA
    cV
    unisng
    sps
    nfceqdf
    syl5ib
    impbid2
end
