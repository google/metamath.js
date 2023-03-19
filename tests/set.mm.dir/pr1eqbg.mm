include "wcel.mm"
include "w3a.mm"
include "wne.mm"
include "wa.mm"
include "wceq.mm"
include "wo.mm"
include "cpr.mm"
include "wb.mm"
include "eqid.mm"
include "biantru.mm"
include "orbi2i.mm"
include "a1i.mm"
include "wn.mm"
include "neneq.mm"
include "adantl.mm"
include "intnanrd.mm"
include "biorf.mm"
include "syl.mm"
include "3simpa.mm"
include "3simpc.mm"
include "jca.mm"
include "adantr.mm"
include "preq12bg.mm"
include "3bitr4d.mm"

theorem pr1eqbg
  let cA: class A
  let cB: class B
  let cC: class C
  let cU: class U
  let cV: class V
  let cX: class X


  assert |- ( ( ( A e. U /\ B e. V /\ C e. X ) /\ A =/= B ) -> ( A = C <-> { A , B } = { B , C } ) )

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
    cX
    wcel
    #
    w3a
    #
    cA
    cB
    wne
    #
    wa
    #
    cA
    cB
    wceq
    #
    cB
    cC
    wceq
    #
    wa
    #
    cA
    cC
    wceq
    #
    wo
    #
    @8
    @9
    cB
    cB
    wceq
    #
    wa
    #
    wo
    #
    @9
    cA
    cB
    cpr
    cB
    cC
    cpr
    wceq
    #
    @10
    @13
    wb
    @5
    @9
    @12
    @8
    @11
    @9
    cB
    eqid
    biantru
    orbi2i
    a1i
    @5
    @8
    wn
    @9
    @10
    wb
    @5
    @6
    @7
    @4
    @6
    wn
    @3
    cA
    cB
    neneq
    adantl
    intnanrd
    @8
    @9
    biorf
    syl
    @5
    @0
    @1
    wa
    #
    @1
    @2
    wa
    #
    wa
    #
    @14
    @13
    wb
    @3
    @17
    @4
    @3
    @15
    @16
    @0
    @1
    @2
    3simpa
    @0
    @1
    @2
    3simpc
    jca
    adantr
    cA
    cB
    cB
    cC
    cU
    cV
    cV
    cX
    preq12bg
    syl
    3bitr4d
end
