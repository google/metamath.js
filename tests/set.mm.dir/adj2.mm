include "cado.mm"
include "cdm.mm"
include "wcel.mm"
include "chil.mm"
include "cfv.mm"
include "csp.mm"
include "co.mm"
include "wceq.mm"
include "w3a.mm"
include "ccj.mm"
include "adj1.mm"
include "simp2.mm"
include "dmadjop.mm"
include "ffvelrnda.mm"
include "3adant2.mm"
include "ax-his1.mm"
include "syl2anc.mm"
include "adjcl.mm"
include "3adant3.mm"
include "simp3.mm"
include "3eqtr3d.mm"
include "cc.mm"
include "wb.mm"
include "hicl.mm"
include "cj11.mm"
include "mpbid.mm"
include "3com23.mm"

theorem adj2
  let cA: class A
  let cB: class B
  let cT: class T
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cC: class C
  let cS: class S


  assert |- ( ( T e. dom adjh /\ A e. ~H /\ B e. ~H ) -> ( ( T ` A ) .ih B ) = ( A .ih ( ( adjh ` T ) ` B ) ) )

  proof
    cT
    cado
    cdm
    wcel
    #
    cB
    chil
    wcel
    #
    cA
    chil
    wcel
    #
    cA
    cT
    cfv
    #
    cB
    csp
    co
    #
    cA
    cB
    cT
    cado
    cfv
    cfv
    #
    csp
    co
    #
    wceq
    #
    @0
    @1
    @2
    w3a
    #
    @4
    ccj
    cfv
    #
    @6
    ccj
    cfv
    #
    wceq
    #
    @7
    @8
    cB
    @3
    csp
    co
    #
    @5
    cA
    csp
    co
    #
    @9
    @10
    cB
    cA
    cT
    adj1
    @8
    @1
    @3
    chil
    wcel
    #
    @12
    @9
    wceq
    @0
    @1
    @2
    simp2
    #
    @0
    @2
    @14
    @1
    @0
    chil
    chil
    cA
    cT
    cT
    dmadjop
    ffvelrnda
    3adant2
    #
    cB
    @3
    ax-his1
    syl2anc
    @8
    @5
    chil
    wcel
    #
    @2
    @13
    @10
    wceq
    @0
    @1
    @17
    @2
    cB
    cT
    adjcl
    3adant3
    #
    @0
    @1
    @2
    simp3
    #
    @5
    cA
    ax-his1
    syl2anc
    3eqtr3d
    @8
    @4
    cc
    wcel
    #
    @6
    cc
    wcel
    #
    @11
    @7
    wb
    @8
    @14
    @1
    @20
    @16
    @15
    @3
    cB
    hicl
    syl2anc
    @8
    @2
    @17
    @21
    @19
    @18
    cA
    @5
    hicl
    syl2anc
    @4
    @6
    cj11
    syl2anc
    mpbid
    3com23
end
