include "cr.mm"
include "wcel.mm"
include "cz.mm"
include "crp.mm"
include "w3a.mm"
include "cmo.mm"
include "co.mm"
include "wa.mm"
include "wceq.mm"
include "cmul.mm"
include "modcl.mm"
include "simpl.mm"
include "jca.mm"
include "3adant2.mm"
include "3simpc.mm"
include "modabs2.mm"
include "modmul1.mm"
include "syl3anc.mm"

theorem modmulmod
  let cA: class A
  let cB: class B
  let cM: class M


  assert |- ( ( A e. RR /\ B e. ZZ /\ M e. RR+ ) -> ( ( ( A mod M ) x. B ) mod M ) = ( ( A x. B ) mod M ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cz
    wcel
    #
    cM
    crp
    wcel
    #
    w3a
    cA
    cM
    cmo
    co
    #
    cr
    wcel
    #
    @0
    wa
    #
    @1
    @2
    wa
    @3
    cM
    cmo
    co
    @3
    wceq
    #
    @3
    cB
    cmul
    co
    cM
    cmo
    co
    cA
    cB
    cmul
    co
    cM
    cmo
    co
    wceq
    @0
    @2
    @5
    @1
    @0
    @2
    wa
    @4
    @0
    cA
    cM
    modcl
    @0
    @2
    simpl
    jca
    3adant2
    @0
    @1
    @2
    3simpc
    @0
    @2
    @6
    @1
    cA
    cM
    modabs2
    3adant2
    @3
    cA
    cB
    cM
    modmul1
    syl3anc
end
