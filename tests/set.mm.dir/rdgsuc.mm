include "con0.mm"
include "wcel.mm"
include "crdg.mm"
include "cdm.mm"
include "csuc.mm"
include "cfv.mm"
include "wceq.mm"
include "wfn.mm"
include "rdgfnon.mm"
include "fndm.mm"
include "ax-mp.mm"
include "eleq2i.mm"
include "rdgsucg.mm"
include "sylbir.mm"

theorem rdgsuc
  let cA: class A
  let cB: class B
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  let vf: setvar f
  let vg: setvar g
  let vv: setvar v
  let vw: setvar w


  assert |- ( B e. On -> ( rec ( F , A ) ` suc B ) = ( F ` ( rec ( F , A ) ` B ) ) )

  proof
    cB
    con0
    wcel
    cB
    cF
    cA
    crdg
    #
    cdm
    #
    wcel
    cB
    csuc
    @0
    cfv
    cB
    @0
    cfv
    cF
    cfv
    wceq
    @1
    con0
    cB
    @0
    con0
    wfn
    @1
    con0
    wceq
    cA
    cF
    rdgfnon
    con0
    @0
    fndm
    ax-mp
    eleq2i
    cA
    cB
    cF
    rdgsucg
    sylbir
end
