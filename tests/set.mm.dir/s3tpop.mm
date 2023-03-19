include "wcel.mm"
include "w3a.mm"
include "cs3.mm"
include "cs2.mm"
include "cs1.mm"
include "cconcat.mm"
include "co.mm"
include "cc0.mm"
include "cop.mm"
include "c1.mm"
include "c2.mm"
include "ctp.mm"
include "df-s3.mm"
include "chash.mm"
include "cfv.mm"
include "csn.mm"
include "cun.mm"
include "cpr.mm"
include "cword.mm"
include "wceq.mm"
include "s2cl.mm"
include "cats1un.mm"
include "stoic3.mm"
include "s2prop.mm"
include "3adant3.mm"
include "s2len.mm"
include "opeq1i.mm"
include "sneqi.mm"
include "a1i.mm"
include "uneq12d.mm"
include "df-tp.mm"
include "eqcomi.mm"
include "3eqtrd.mm"
include "syl5eq.mm"

theorem s3tpop
  let cA: class A
  let cB: class B
  let cC: class C
  let cS: class S


  assert |- ( ( A e. S /\ B e. S /\ C e. S ) -> <" A B C "> = { <. 0 , A >. , <. 1 , B >. , <. 2 , C >. } )

  proof
    cA
    cS
    wcel
    #
    cB
    cS
    wcel
    #
    cC
    cS
    wcel
    #
    w3a
    #
    cA
    cB
    cC
    cs3
    cA
    cB
    cs2
    #
    cC
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
    c2
    cC
    cop
    #
    ctp
    #
    cA
    cB
    cC
    df-s3
    @3
    @5
    @4
    @4
    chash
    cfv
    #
    cC
    cop
    #
    csn
    #
    cun
    #
    @6
    @7
    cpr
    #
    @8
    csn
    #
    cun
    #
    @9
    @0
    @1
    @4
    cS
    cword
    wcel
    @2
    @5
    @13
    wceq
    cA
    cB
    cS
    s2cl
    @4
    cC
    cS
    cats1un
    stoic3
    @3
    @4
    @14
    @12
    @15
    @0
    @1
    @4
    @14
    wceq
    @2
    cA
    cB
    cS
    s2prop
    3adant3
    @12
    @15
    wceq
    @3
    @11
    @8
    @10
    c2
    cC
    cA
    cB
    s2len
    opeq1i
    sneqi
    a1i
    uneq12d
    @16
    @9
    wceq
    @3
    @9
    @16
    @6
    @7
    @8
    df-tp
    eqcomi
    a1i
    3eqtrd
    syl5eq
end
