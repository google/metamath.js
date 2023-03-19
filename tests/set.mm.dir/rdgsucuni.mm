include "con0.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "wlim.mm"
include "wn.mm"
include "w3a.mm"
include "crdg.mm"
include "cfv.mm"
include "cuni.mm"
include "csuc.mm"
include "onsucuni3.mm"
include "fveq2d.mm"
include "wceq.mm"
include "onuni.mm"
include "3ad2ant1.mm"
include "rdgsuc.mm"
include "syl.mm"
include "eqtrd.mm"

theorem rdgsucuni
  let cB: class B
  let cF: class F
  let cI: class I


  assert |- ( ( B e. On /\ B =/= (/) /\ -. Lim B ) -> ( rec ( F , I ) ` B ) = ( F ` ( rec ( F , I ) ` U. B ) ) )

  proof
    cB
    con0
    wcel
    #
    cB
    c0
    wne
    #
    cB
    wlim
    wn
    #
    w3a
    #
    cB
    cF
    cI
    crdg
    #
    cfv
    cB
    cuni
    #
    csuc
    #
    @4
    cfv
    #
    @5
    @4
    cfv
    cF
    cfv
    #
    @3
    cB
    @6
    @4
    cB
    onsucuni3
    fveq2d
    @3
    @5
    con0
    wcel
    #
    @7
    @8
    wceq
    @0
    @1
    @9
    @2
    cB
    onuni
    3ad2ant1
    cI
    @5
    cF
    rdgsuc
    syl
    eqtrd
end
