include "wcel.mm"
include "wa.mm"
include "cs2.mm"
include "cs1.mm"
include "cconcat.mm"
include "co.mm"
include "cc0.mm"
include "cop.mm"
include "c1.mm"
include "cpr.mm"
include "df-s2.mm"
include "chash.mm"
include "cfv.mm"
include "csn.mm"
include "cun.mm"
include "cword.mm"
include "wceq.mm"
include "s1cl.mm"
include "cats1un.mm"
include "sylan.mm"
include "s1val.mm"
include "adantr.mm"
include "uneq1d.mm"
include "df-pr.mm"
include "s1len.mm"
include "a1i.mm"
include "opeq1d.mm"
include "preq2d.mm"
include "syl5eqr.mm"
include "3eqtrd.mm"
include "syl5eq.mm"

theorem s2prop
  let cA: class A
  let cB: class B
  let cS: class S


  assert |- ( ( A e. S /\ B e. S ) -> <" A B "> = { <. 0 , A >. , <. 1 , B >. } )

  proof
    cA
    cS
    wcel
    #
    cB
    cS
    wcel
    #
    wa
    #
    cA
    cB
    cs2
    cA
    cs1
    #
    cB
    cs1
    cconcat
    co
    #
    cc0
    cA
    cop
    #
    c1
    cB
    cop
    #
    cpr
    #
    cA
    cB
    df-s2
    @2
    @4
    @3
    @3
    chash
    cfv
    #
    cB
    cop
    #
    csn
    #
    cun
    #
    @5
    csn
    #
    @10
    cun
    #
    @7
    @0
    @3
    cS
    cword
    wcel
    @1
    @4
    @11
    wceq
    cA
    cS
    s1cl
    @3
    cB
    cS
    cats1un
    sylan
    @2
    @3
    @12
    @10
    @0
    @3
    @12
    wceq
    @1
    cA
    cS
    s1val
    adantr
    uneq1d
    @2
    @13
    @5
    @9
    cpr
    @7
    @5
    @9
    df-pr
    @2
    @9
    @6
    @5
    @2
    @8
    c1
    cB
    @8
    c1
    wceq
    @2
    cA
    s1len
    a1i
    opeq1d
    preq2d
    syl5eqr
    3eqtrd
    syl5eq
end
