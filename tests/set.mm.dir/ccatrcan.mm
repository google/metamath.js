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
include "ccatopth2.mm"
include "mp3an3.mm"
include "3impdir.mm"
include "biantru.mm"
include "syl6bbr.mm"

theorem ccatrcan
  let cA: class A
  let cB: class B
  let cC: class C
  let cX: class X


  assert |- ( ( A e. Word X /\ B e. Word X /\ C e. Word X ) -> ( ( A ++ C ) = ( B ++ C ) <-> A = B ) )

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
    cA
    cC
    cconcat
    co
    cB
    cC
    cconcat
    co
    wceq
    #
    cA
    cB
    wceq
    #
    cC
    cC
    wceq
    #
    wa
    #
    @5
    @1
    @3
    @2
    @4
    @7
    wb
    #
    @1
    @3
    wa
    @2
    @3
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
    cA
    cC
    cB
    cC
    cX
    ccatopth2
    mp3an3
    3impdir
    @6
    @5
    cC
    eqid
    biantru
    syl6bbr
end
