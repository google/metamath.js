include "wfn.mm"
include "wa.mm"
include "wss.mm"
include "cres.mm"
include "wceq.mm"
include "cv.mm"
include "cfv.mm"
include "wral.mm"
include "fnresdm.mm"
include "ad2antlr.mm"
include "eqcomd.mm"
include "eqeq2d.mm"
include "wb.mm"
include "ssid.mm"
include "fvreseq0.mm"
include "mpanr2.mm"
include "bitrd.mm"

theorem fvreseq1
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G

  disjoint B x
  disjoint F x
  disjoint G x
  assert |- ( ( ( F Fn A /\ G Fn B ) /\ B C_ A ) -> ( ( F |` B ) = G <-> A. x e. B ( F ` x ) = ( G ` x ) ) )

  proof
    cF
    cA
    wfn
    #
    cG
    cB
    wfn
    #
    wa
    #
    cB
    cA
    wss
    #
    wa
    #
    cF
    cB
    cres
    #
    cG
    wceq
    @5
    cG
    cB
    cres
    #
    wceq
    #
    vx
    cv
    #
    cF
    cfv
    @8
    cG
    cfv
    wceq
    vx
    cB
    wral
    #
    @4
    cG
    @6
    @5
    @4
    @6
    cG
    @1
    @6
    cG
    wceq
    @0
    @3
    cB
    cG
    fnresdm
    ad2antlr
    eqcomd
    eqeq2d
    @2
    @3
    cB
    cB
    wss
    @7
    @9
    wb
    cB
    ssid
    vx
    cA
    cB
    cB
    cF
    cG
    fvreseq0
    mpanr2
    bitrd
end
