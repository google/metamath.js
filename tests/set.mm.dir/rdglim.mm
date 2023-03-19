include "wcel.mm"
include "wlim.mm"
include "crdg.mm"
include "cdm.mm"
include "cfv.mm"
include "cima.mm"
include "cuni.mm"
include "wceq.mm"
include "wa.mm"
include "con0.mm"
include "limelon.mm"
include "wfn.mm"
include "rdgfnon.mm"
include "fndm.mm"
include "ax-mp.mm"
include "syl6eleqr.mm"
include "rdglimg.mm"
include "sylancom.mm"

theorem rdglim
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  let vg: setvar g
  let vv: setvar v
  let vw: setvar w


  assert |- ( ( B e. C /\ Lim B ) -> ( rec ( F , A ) ` B ) = U. ( rec ( F , A ) " B ) )

  proof
    cB
    cC
    wcel
    #
    cB
    wlim
    #
    cB
    cF
    cA
    crdg
    #
    cdm
    #
    wcel
    cB
    @2
    cfv
    @2
    cB
    cima
    cuni
    wceq
    @0
    @1
    wa
    cB
    con0
    @3
    cB
    cC
    limelon
    @2
    con0
    wfn
    @3
    con0
    wceq
    cA
    cF
    rdgfnon
    con0
    @2
    fndm
    ax-mp
    syl6eleqr
    cA
    cB
    cF
    rdglimg
    sylancom
end
