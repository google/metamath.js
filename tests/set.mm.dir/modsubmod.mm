include "cr.mm"
include "wcel.mm"
include "crp.mm"
include "w3a.mm"
include "cmo.mm"
include "co.mm"
include "modcl.mm"
include "3adant2.mm"
include "simp1.mm"
include "simp2.mm"
include "simp3.mm"
include "wceq.mm"
include "modabs2.mm"
include "eqidd.mm"
include "modsub12d.mm"

theorem modsubmod
  let cA: class A
  let cB: class B
  let cM: class M


  assert |- ( ( A e. RR /\ B e. RR /\ M e. RR+ ) -> ( ( ( A mod M ) - B ) mod M ) = ( ( A - B ) mod M ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    cM
    crp
    wcel
    #
    w3a
    #
    cA
    cM
    cmo
    co
    #
    cA
    cB
    cB
    cM
    @0
    @2
    @4
    cr
    wcel
    @1
    cA
    cM
    modcl
    3adant2
    @0
    @1
    @2
    simp1
    @0
    @1
    @2
    simp2
    #
    @5
    @0
    @1
    @2
    simp3
    @0
    @2
    @4
    cM
    cmo
    co
    @4
    wceq
    @1
    cA
    cM
    modabs2
    3adant2
    @3
    cB
    cM
    cmo
    co
    eqidd
    modsub12d
end
