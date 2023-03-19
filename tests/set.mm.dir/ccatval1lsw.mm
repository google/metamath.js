include "cword.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "w3a.mm"
include "chash.mm"
include "cfv.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cconcat.mm"
include "clsw.mm"
include "cc0.mm"
include "cfzo.mm"
include "wceq.mm"
include "cn.mm"
include "lennncl.mm"
include "3adant2.mm"
include "fzo0end.mm"
include "syl.mm"
include "ccatval1.mm"
include "syld3an3.mm"
include "lsw.mm"
include "3ad2ant1.mm"
include "eqtr4d.mm"

theorem ccatval1lsw
  let cA: class A
  let cB: class B
  let cV: class V


  assert |- ( ( A e. Word V /\ B e. Word V /\ A =/= (/) ) -> ( ( A ++ B ) ` ( ( # ` A ) - 1 ) ) = ( lastS ` A ) )

  proof
    cA
    cV
    cword
    #
    wcel
    #
    cB
    @0
    wcel
    #
    cA
    c0
    wne
    #
    w3a
    #
    cA
    chash
    cfv
    #
    c1
    cmin
    co
    #
    cA
    cB
    cconcat
    co
    cfv
    #
    @6
    cA
    cfv
    #
    cA
    clsw
    cfv
    #
    @1
    @2
    @3
    @6
    cc0
    @5
    cfzo
    co
    wcel
    #
    @7
    @8
    wceq
    @4
    @5
    cn
    wcel
    #
    @10
    @1
    @3
    @11
    @2
    cV
    cA
    lennncl
    3adant2
    @5
    fzo0end
    syl
    cV
    cA
    cB
    @6
    ccatval1
    syld3an3
    @1
    @2
    @9
    @8
    wceq
    @3
    cA
    @0
    lsw
    3ad2ant1
    eqtr4d
end
