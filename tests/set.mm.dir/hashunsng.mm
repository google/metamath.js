include "cfn.mm"
include "wcel.mm"
include "wn.mm"
include "wa.mm"
include "csn.mm"
include "cun.mm"
include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "wceq.mm"
include "cin.mm"
include "c0.mm"
include "disjsn.mm"
include "snfi.mm"
include "hashun.mm"
include "mp3an2.mm"
include "sylan2br.mm"
include "hashsng.mm"
include "oveq2d.mm"
include "sylan9eq.mm"
include "expcom.mm"

theorem hashunsng
  let cA: class A
  let cB: class B
  let cV: class V


  assert |- ( B e. V -> ( ( A e. Fin /\ -. B e. A ) -> ( # ` ( A u. { B } ) ) = ( ( # ` A ) + 1 ) ) )

  proof
    cA
    cfn
    wcel
    #
    cB
    cA
    wcel
    wn
    #
    wa
    #
    cB
    cV
    wcel
    #
    cA
    cB
    csn
    #
    cun
    chash
    cfv
    #
    cA
    chash
    cfv
    #
    c1
    caddc
    co
    #
    wceq
    @2
    @3
    @5
    @6
    @4
    chash
    cfv
    #
    caddc
    co
    #
    @7
    @1
    @0
    cA
    @4
    cin
    c0
    wceq
    #
    @5
    @9
    wceq
    #
    cA
    cB
    disjsn
    @0
    @4
    cfn
    wcel
    @10
    @11
    cB
    snfi
    cA
    @4
    hashun
    mp3an2
    sylan2br
    @3
    @8
    c1
    @6
    caddc
    cB
    cV
    hashsng
    oveq2d
    sylan9eq
    expcom
end
