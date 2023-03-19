include "wcel.mm"
include "wss.mm"
include "w3a.mm"
include "wf.mm"
include "cima.mm"
include "wa.mm"
include "cmap.mm"
include "co.mm"
include "cin.mm"
include "wceq.mm"
include "wb.mm"
include "simp3.mm"
include "sseqin2.mm"
include "biimpi.mm"
include "eqcomd.mm"
include "k0004lem1.mm"
include "3syl.mm"
include "simp2.mm"
include "simp1.mm"
include "elmapd.mm"
include "anbi1d.mm"
include "cvv.mm"
include "ssexd.mm"
include "3bitr4d.mm"

theorem k0004lem2
  let cA: class A
  let cB: class B
  let cC: class C
  let cU: class U
  let cF: class F
  let cV: class V


  assert |- ( ( A e. U /\ B e. V /\ C C_ B ) -> ( ( F e. ( B ^m A ) /\ ( F " A ) C_ C ) <-> F e. ( C ^m A ) ) )

  proof
    cA
    cU
    wcel
    #
    cB
    cV
    wcel
    #
    cC
    cB
    wss
    #
    w3a
    #
    cA
    cB
    cF
    wf
    #
    cF
    cA
    cima
    cC
    wss
    #
    wa
    #
    cA
    cC
    cF
    wf
    #
    cF
    cB
    cA
    cmap
    co
    wcel
    #
    @5
    wa
    cF
    cC
    cA
    cmap
    co
    wcel
    @3
    @2
    cC
    cB
    cC
    cin
    #
    wceq
    @6
    @7
    wb
    @0
    @1
    @2
    simp3
    #
    @2
    @9
    cC
    @2
    @9
    cC
    wceq
    cC
    cB
    sseqin2
    biimpi
    eqcomd
    cA
    cB
    cC
    cC
    cF
    k0004lem1
    3syl
    @3
    @8
    @4
    @5
    @3
    cB
    cA
    cF
    cV
    cU
    @0
    @1
    @2
    simp2
    #
    @0
    @1
    @2
    simp1
    #
    elmapd
    anbi1d
    @3
    cC
    cA
    cF
    cvv
    cU
    @3
    cC
    cB
    cV
    @11
    @10
    ssexd
    @12
    elmapd
    3bitr4d
end
