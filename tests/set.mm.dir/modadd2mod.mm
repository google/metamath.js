include "cr.mm"
include "wcel.mm"
include "crp.mm"
include "w3a.mm"
include "cmo.mm"
include "co.mm"
include "caddc.mm"
include "cc.mm"
include "recn.mm"
include "3ad2ant2.mm"
include "wa.mm"
include "modcl.mm"
include "recnd.mm"
include "3adant2.mm"
include "addcomd.mm"
include "oveq1d.mm"
include "modaddmod.mm"
include "wceq.mm"
include "addcom.mm"
include "syl2an.mm"
include "3adant3.mm"
include "3eqtrd.mm"

theorem modadd2mod
  let cA: class A
  let cB: class B
  let cM: class M


  assert |- ( ( A e. RR /\ B e. RR /\ M e. RR+ ) -> ( ( B + ( A mod M ) ) mod M ) = ( ( B + A ) mod M ) )

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
    cB
    cA
    cM
    cmo
    co
    #
    caddc
    co
    #
    cM
    cmo
    co
    @4
    cB
    caddc
    co
    #
    cM
    cmo
    co
    cA
    cB
    caddc
    co
    #
    cM
    cmo
    co
    #
    cB
    cA
    caddc
    co
    #
    cM
    cmo
    co
    #
    @3
    @5
    @6
    cM
    cmo
    @3
    cB
    @4
    @1
    @0
    cB
    cc
    wcel
    #
    @2
    cB
    recn
    #
    3ad2ant2
    @0
    @2
    @4
    cc
    wcel
    @1
    @0
    @2
    wa
    @4
    cA
    cM
    modcl
    recnd
    3adant2
    addcomd
    oveq1d
    cA
    cB
    cM
    modaddmod
    @0
    @1
    @8
    @10
    wceq
    @2
    @0
    @1
    wa
    @7
    @9
    cM
    cmo
    @0
    cA
    cc
    wcel
    @11
    @7
    @9
    wceq
    @1
    cA
    recn
    @12
    cA
    cB
    addcom
    syl2an
    oveq1d
    3adant3
    3eqtrd
end
