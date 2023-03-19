include "wcel.mm"
include "wa.mm"
include "cs4.mm"
include "cs3.mm"
include "cs1.mm"
include "cconcat.mm"
include "co.mm"
include "cc0.mm"
include "cop.mm"
include "c1.mm"
include "cpr.mm"
include "c2.mm"
include "c3.mm"
include "cun.mm"
include "df-s4.mm"
include "cs2.mm"
include "chash.mm"
include "cfv.mm"
include "csn.mm"
include "cword.mm"
include "wceq.mm"
include "simpl.mm"
include "adantr.mm"
include "simpr.mm"
include "adantl.mm"
include "s3cld.mm"
include "cats1un.mm"
include "syl2anc.mm"
include "df-s3.mm"
include "s2cl.mm"
include "syl5eq.mm"
include "s2prop.mm"
include "uneq1d.mm"
include "eqtrd.mm"
include "unass.mm"
include "a1i.mm"
include "df-pr.mm"
include "s2len.mm"
include "opeq1d.mm"
include "s3len.mm"
include "preq12d.mm"
include "syl5eqr.mm"
include "uneq2d.mm"
include "3eqtrd.mm"

theorem s4prop
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cS: class S


  assert |- ( ( ( A e. S /\ B e. S ) /\ ( C e. S /\ D e. S ) ) -> <" A B C D "> = ( { <. 0 , A >. , <. 1 , B >. } u. { <. 2 , C >. , <. 3 , D >. } ) )

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
    cC
    cS
    wcel
    #
    cD
    cS
    wcel
    #
    wa
    #
    wa
    #
    cA
    cB
    cC
    cD
    cs4
    cA
    cB
    cC
    cs3
    #
    cD
    cs1
    cconcat
    co
    #
    cc0
    cA
    cop
    c1
    cB
    cop
    cpr
    #
    c2
    cC
    cop
    #
    c3
    cD
    cop
    #
    cpr
    #
    cun
    #
    cA
    cB
    cC
    cD
    df-s4
    @6
    @8
    @9
    cA
    cB
    cs2
    #
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
    @7
    chash
    cfv
    #
    cD
    cop
    #
    csn
    #
    cun
    #
    @9
    @17
    @21
    cun
    #
    cun
    #
    @13
    @6
    @8
    @7
    @21
    cun
    #
    @22
    @6
    @7
    cS
    cword
    #
    wcel
    @4
    @8
    @25
    wceq
    @6
    cA
    cB
    cC
    cS
    @2
    @0
    @5
    @0
    @1
    simpl
    adantr
    @2
    @1
    @5
    @0
    @1
    simpr
    adantr
    @5
    @3
    @2
    @3
    @4
    simpl
    adantl
    #
    s3cld
    @5
    @4
    @2
    @3
    @4
    simpr
    adantl
    @7
    cD
    cS
    cats1un
    syl2anc
    @6
    @7
    @18
    @21
    @6
    @7
    @14
    @17
    cun
    #
    @18
    @6
    @7
    @14
    cC
    cs1
    cconcat
    co
    #
    @28
    cA
    cB
    cC
    df-s3
    @6
    @14
    @26
    wcel
    #
    @3
    @29
    @28
    wceq
    @2
    @30
    @5
    cA
    cB
    cS
    s2cl
    adantr
    @27
    @14
    cC
    cS
    cats1un
    syl2anc
    syl5eq
    @6
    @14
    @9
    @17
    @2
    @14
    @9
    wceq
    @5
    cA
    cB
    cS
    s2prop
    adantr
    uneq1d
    eqtrd
    uneq1d
    eqtrd
    @22
    @24
    wceq
    @6
    @9
    @17
    @21
    unass
    a1i
    @6
    @23
    @12
    @9
    @6
    @23
    @16
    @20
    cpr
    @12
    @16
    @20
    df-pr
    @6
    @16
    @10
    @20
    @11
    @6
    @15
    c2
    cC
    @15
    c2
    wceq
    @6
    cA
    cB
    s2len
    a1i
    opeq1d
    @6
    @19
    c3
    cD
    @19
    c3
    wceq
    @6
    cA
    cB
    cC
    s3len
    a1i
    opeq1d
    preq12d
    syl5eqr
    uneq2d
    3eqtrd
    syl5eq
end
