include "com.mm"
include "wcel.mm"
include "csuc.mm"
include "crdg.mm"
include "cfv.mm"
include "cres.mm"
include "cdm.mm"
include "wceq.mm"
include "wlim.mm"
include "wss.mm"
include "rdgdmlim.mm"
include "limomss.mm"
include "ax-mp.mm"
include "sseli.mm"
include "rdgsucg.mm"
include "syl.mm"
include "peano2b.mm"
include "fvres.mm"
include "sylbi.mm"
include "fveq2d.mm"
include "3eqtr4d.mm"

theorem frsuc
  let cA: class A
  let cB: class B
  let cF: class F


  assert |- ( B e. _om -> ( ( rec ( F , A ) |` _om ) ` suc B ) = ( F ` ( ( rec ( F , A ) |` _om ) ` B ) ) )

  proof
    cB
    com
    wcel
    #
    cB
    csuc
    #
    cF
    cA
    crdg
    #
    cfv
    #
    cB
    @2
    cfv
    #
    cF
    cfv
    #
    @1
    @2
    com
    cres
    #
    cfv
    #
    cB
    @6
    cfv
    #
    cF
    cfv
    @0
    cB
    @2
    cdm
    #
    wcel
    @3
    @5
    wceq
    com
    @9
    cB
    @9
    wlim
    com
    @9
    wss
    cA
    cF
    rdgdmlim
    @9
    limomss
    ax-mp
    sseli
    cA
    cB
    cF
    rdgsucg
    syl
    @0
    @1
    com
    wcel
    @7
    @3
    wceq
    cB
    peano2b
    @1
    com
    @2
    fvres
    sylbi
    @0
    @8
    @4
    cF
    cB
    com
    @2
    fvres
    fveq2d
    3eqtr4d
end
