include "cumgr.mm"
include "wcel.mm"
include "cpr.mm"
include "w3a.mm"
include "wne.mm"
include "wa.mm"
include "cvtx.mm"
include "cfv.mm"
include "umgredgne.mm"
include "ex.mm"
include "anim12d.mm"
include "3impib.mm"
include "eqid.mm"
include "umgrpredgv.mm"
include "simpld.mm"
include "3adant3.mm"
include "3adant2.mm"
include "simprd.mm"
include "3jca.mm"
include "jca.mm"

theorem umgr2adedgwlklem
  let cA: class A
  let cB: class B
  let cC: class C
  let cE: class E
  let cG: class G
  assume umgr2adedgwlk.e: |- E = ( Edg ` G )


  assert |- ( ( G e. UMGraph /\ { A , B } e. E /\ { B , C } e. E ) -> ( ( A =/= B /\ B =/= C ) /\ ( A e. ( Vtx ` G ) /\ B e. ( Vtx ` G ) /\ C e. ( Vtx ` G ) ) ) )

  proof
    cG
    cumgr
    wcel
    #
    cA
    cB
    cpr
    cE
    wcel
    #
    cB
    cC
    cpr
    cE
    wcel
    #
    w3a
    #
    cA
    cB
    wne
    #
    cB
    cC
    wne
    #
    wa
    #
    cA
    cG
    cvtx
    cfv
    #
    wcel
    #
    cB
    @7
    wcel
    #
    cC
    @7
    wcel
    #
    w3a
    @0
    @1
    @2
    @6
    @0
    @1
    @4
    @2
    @5
    @0
    @1
    @4
    cE
    cG
    cA
    cB
    umgr2adedgwlk.e
    umgredgne
    ex
    @0
    @2
    @5
    cE
    cG
    cB
    cC
    umgr2adedgwlk.e
    umgredgne
    ex
    anim12d
    3impib
    @3
    @8
    @9
    @10
    @0
    @1
    @8
    @2
    @0
    @1
    wa
    @8
    @9
    cE
    cG
    cA
    cB
    @7
    @7
    eqid
    #
    umgr2adedgwlk.e
    umgrpredgv
    simpld
    3adant3
    @0
    @2
    @9
    @1
    @0
    @2
    wa
    #
    @9
    @10
    cE
    cG
    cB
    cC
    @7
    @11
    umgr2adedgwlk.e
    umgrpredgv
    #
    simpld
    3adant2
    @0
    @2
    @10
    @1
    @12
    @9
    @10
    @13
    simprd
    3adant2
    3jca
    jca
end
