include "cz.mm"
include "wcel.mm"
include "cr.mm"
include "crp.mm"
include "w3a.mm"
include "cmo.mm"
include "co.mm"
include "cmul.mm"
include "cc.mm"
include "zcn.mm"
include "3ad2ant1.mm"
include "simp2.mm"
include "simp3.mm"
include "modcld.mm"
include "recnd.mm"
include "mulcomd.mm"
include "oveq1d.mm"
include "wceq.mm"
include "modmulmod.mm"
include "3com12.mm"
include "wa.mm"
include "recn.mm"
include "anim12ci.mm"
include "3adant3.mm"
include "mulcom.mm"
include "syl.mm"
include "3eqtrd.mm"

theorem modmulmodr
  let cA: class A
  let cB: class B
  let cM: class M


  assert |- ( ( A e. ZZ /\ B e. RR /\ M e. RR+ ) -> ( ( A x. ( B mod M ) ) mod M ) = ( ( A x. B ) mod M ) )

  proof
    cA
    cz
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
    cB
    cM
    cmo
    co
    #
    cmul
    co
    #
    cM
    cmo
    co
    @4
    cA
    cmul
    co
    #
    cM
    cmo
    co
    #
    cB
    cA
    cmul
    co
    #
    cM
    cmo
    co
    #
    cA
    cB
    cmul
    co
    #
    cM
    cmo
    co
    @3
    @5
    @6
    cM
    cmo
    @3
    cA
    @4
    @0
    @1
    cA
    cc
    wcel
    #
    @2
    cA
    zcn
    #
    3ad2ant1
    @3
    @4
    @3
    cB
    cM
    @0
    @1
    @2
    simp2
    @0
    @1
    @2
    simp3
    modcld
    recnd
    mulcomd
    oveq1d
    @1
    @0
    @2
    @7
    @9
    wceq
    cB
    cA
    cM
    modmulmod
    3com12
    @3
    @8
    @10
    cM
    cmo
    @3
    cB
    cc
    wcel
    #
    @11
    wa
    #
    @8
    @10
    wceq
    @0
    @1
    @14
    @2
    @0
    @11
    @1
    @13
    @12
    cB
    recn
    anim12ci
    3adant3
    cB
    cA
    mulcom
    syl
    oveq1d
    3eqtrd
end
