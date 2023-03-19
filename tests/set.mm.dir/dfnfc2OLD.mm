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
include "wa.mm"
include "csn.mm"
include "cuni.mm"
include "simpr.mm"
include "df-nfc.mm"
include "velsn.mm"
include "nfbii.mm"
include "albii.mm"
include "bitri.mm"
include "sylibr.mm"
include "nfunid.mm"
include "nfa1.mm"
include "nfnf1.mm"
include "nfal.mm"
include "nfan.mm"
include "unisng.mm"
include "sps.mm"
include "adantr.mm"
include "nfceqdf.mm"
include "mpbid.mm"
include "ex.mm"
include "impbid2.mm"

theorem dfnfc2OLD
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
    @1
    @6
    @2
    @1
    @6
    wa
    #
    vx
    cA
    csn
    #
    cuni
    #
    wnfc
    @2
    @7
    vx
    @8
    @7
    @6
    vx
    @8
    wnfc
    #
    @1
    @6
    simpr
    @10
    @3
    @8
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
    @8
    df-nfc
    @12
    @5
    vy
    @11
    @4
    vx
    vy
    cA
    velsn
    nfbii
    albii
    bitri
    sylibr
    nfunid
    @7
    vx
    @9
    cA
    @1
    @6
    vx
    @0
    vx
    nfa1
    @5
    vx
    vy
    @4
    vx
    nfnf1
    nfal
    nfan
    @1
    @9
    cA
    wceq
    #
    @6
    @0
    @13
    vx
    cA
    cV
    unisng
    sps
    adantr
    nfceqdf
    mpbid
    ex
    impbid2
end
