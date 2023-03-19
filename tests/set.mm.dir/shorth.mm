include "csh.mm"
include "wcel.mm"
include "cort.mm"
include "cfv.mm"
include "wss.mm"
include "wa.mm"
include "csp.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "ssel.mm"
include "anim1d.mm"
include "imp.mm"
include "ancomd.mm"
include "shocorth.mm"
include "chil.mm"
include "wb.mm"
include "shss.mm"
include "sseld.mm"
include "shocss.mm"
include "anim12d.mm"
include "orthcom.mm"
include "syl.mm"
include "mpbid.mm"
include "sylan2.mm"
include "exp32.mm"

theorem shorth
  let cA: class A
  let cB: class B
  let cG: class G
  let cH: class H
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z


  assert |- ( H e. SH -> ( G C_ ( _|_ ` H ) -> ( ( A e. G /\ B e. H ) -> ( A .ih B ) = 0 ) ) )

  proof
    cH
    csh
    wcel
    #
    cG
    cH
    cort
    cfv
    #
    wss
    #
    cA
    cG
    wcel
    #
    cB
    cH
    wcel
    #
    wa
    #
    cA
    cB
    csp
    co
    cc0
    wceq
    #
    @2
    @5
    wa
    #
    @0
    @4
    cA
    @1
    wcel
    #
    wa
    #
    @6
    @7
    @8
    @4
    @2
    @5
    @8
    @4
    wa
    @2
    @3
    @8
    @4
    cG
    @1
    cA
    ssel
    anim1d
    imp
    ancomd
    @0
    @9
    wa
    #
    cB
    cA
    csp
    co
    cc0
    wceq
    #
    @6
    @0
    @9
    @11
    cB
    cA
    cH
    shocorth
    imp
    @10
    cB
    chil
    wcel
    #
    cA
    chil
    wcel
    #
    wa
    #
    @11
    @6
    wb
    @0
    @9
    @14
    @0
    @4
    @12
    @8
    @13
    @0
    cH
    chil
    cB
    cH
    shss
    sseld
    @0
    @1
    chil
    cA
    cH
    shocss
    sseld
    anim12d
    imp
    cB
    cA
    orthcom
    syl
    mpbid
    sylan2
    exp32
end
