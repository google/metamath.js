include "cv.mm"
include "cfv.mm"
include "wne.mm"
include "wrex.mm"
include "wfn.mm"
include "wb.mm"
include "wa.mm"
include "wceq.mm"
include "wral.mm"
include "wn.mm"
include "eqfnfv.mm"
include "necon3abid.mm"
include "df-ne.mm"
include "rexbii.mm"
include "rexnal.mm"
include "bitri.mm"
include "syl6bbr.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "nfv.mm"
include "nfcii.mm"
include "nfcv.mm"
include "nffv.mm"
include "nfne.mm"
include "fveq2.mm"
include "neeq12d.mm"
include "cbvrex.mm"
include "sylibr.mm"

theorem bnj1542
  let wph: wff ph
  let vx: setvar x
  let vw: setvar w
  let cA: class A
  let cF: class F
  let cG: class G
  let vy: setvar y
  assume bnj1542.1: |- ( ph -> F Fn A )
  assume bnj1542.2: |- ( ph -> G Fn A )
  assume bnj1542.3: |- ( ph -> F =/= G )
  assume bnj1542.4: |- ( w e. F -> A. x w e. F )

  disjoint A x
  disjoint F w
  disjoint G w
  disjoint G x
  disjoint w x
  disjoint A y
  disjoint x y
  disjoint F y
  disjoint w y
  disjoint G y
  assert |- ( ph -> E. x e. A ( F ` x ) =/= ( G ` x ) )

  proof
    wph
    vy
    cv
    #
    cF
    cfv
    #
    @0
    cG
    cfv
    #
    wne
    #
    vy
    cA
    wrex
    #
    vx
    cv
    #
    cF
    cfv
    #
    @5
    cG
    cfv
    #
    wne
    #
    vx
    cA
    wrex
    wph
    cF
    cG
    wne
    #
    @4
    bnj1542.3
    wph
    cF
    cA
    wfn
    #
    cG
    cA
    wfn
    #
    @9
    @4
    wb
    bnj1542.1
    bnj1542.2
    @10
    @11
    wa
    #
    @9
    @1
    @2
    wceq
    #
    vy
    cA
    wral
    #
    wn
    #
    @4
    @12
    @14
    cF
    cG
    vy
    cA
    cF
    cG
    eqfnfv
    necon3abid
    @4
    @13
    wn
    #
    vy
    cA
    wrex
    @15
    @3
    @16
    vy
    cA
    @1
    @2
    df-ne
    rexbii
    @13
    vy
    cA
    rexnal
    bitri
    syl6bbr
    syl2anc
    mpbid
    @8
    @3
    vx
    vy
    cA
    @8
    vy
    nfv
    vx
    @1
    @2
    vx
    @0
    cF
    vx
    vw
    cF
    bnj1542.4
    nfcii
    vx
    @0
    nfcv
    nffv
    vx
    @2
    nfcv
    nfne
    @5
    @0
    wceq
    @6
    @1
    @7
    @2
    @5
    @0
    cF
    fveq2
    @5
    @0
    cG
    fveq2
    neeq12d
    cbvrex
    sylibr
end
