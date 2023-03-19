include "cword.mm"
include "wcel.mm"
include "w3a.mm"
include "cconcat.mm"
include "co.mm"
include "wceq.mm"
include "wa.mm"
include "wb.mm"
include "chash.mm"
include "cfv.mm"
include "eqid.mm"
include "ccatopth.mm"
include "mp3an3.mm"
include "3impdi.mm"
include "3coml.mm"
include "biantrur.mm"
include "syl6bbr.mm"

theorem ccatlcan
  let cA: class A
  let cB: class B
  let cC: class C
  let cX: class X


  assert |- ( ( A e. Word X /\ B e. Word X /\ C e. Word X ) -> ( ( C ++ A ) = ( C ++ B ) <-> A = B ) )

  proof
    cA
    cX
    cword
    #
    wcel
    #
    cB
    @0
    wcel
    #
    cC
    @0
    wcel
    #
    w3a
    cC
    cA
    cconcat
    co
    cC
    cB
    cconcat
    co
    wceq
    #
    cC
    cC
    wceq
    #
    cA
    cB
    wceq
    #
    wa
    #
    @6
    @3
    @1
    @2
    @4
    @7
    wb
    #
    @3
    @1
    @2
    @8
    @3
    @1
    wa
    @3
    @2
    wa
    cC
    chash
    cfv
    #
    @9
    wceq
    @8
    @9
    eqid
    cC
    cA
    cC
    cB
    cX
    ccatopth
    mp3an3
    3impdi
    3coml
    @5
    @6
    cC
    eqid
    biantrur
    syl6bbr
end
