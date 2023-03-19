include "wcel.mm"
include "wa.mm"
include "cs2.mm"
include "wceq.mm"
include "cs1.mm"
include "cconcat.mm"
include "co.mm"
include "df-s2.mm"
include "a1i.mm"
include "eqeq12d.mm"
include "cword.mm"
include "chash.mm"
include "cfv.mm"
include "wb.mm"
include "s1cl.mm"
include "anim12i.mm"
include "adantr.mm"
include "adantl.mm"
include "c1.mm"
include "s1len.mm"
include "eqtr4i.mm"
include "ccatopth.mm"
include "syl3anc.mm"
include "bitrd.mm"

theorem s2eq2s1eq
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cV: class V


  assert |- ( ( ( A e. V /\ B e. V ) /\ ( C e. V /\ D e. V ) ) -> ( <" A B "> = <" C D "> <-> ( <" A "> = <" C "> /\ <" B "> = <" D "> ) ) )

  proof
    cA
    cV
    wcel
    #
    cB
    cV
    wcel
    #
    wa
    #
    cC
    cV
    wcel
    #
    cD
    cV
    wcel
    #
    wa
    #
    wa
    #
    cA
    cB
    cs2
    #
    cC
    cD
    cs2
    #
    wceq
    cA
    cs1
    #
    cB
    cs1
    #
    cconcat
    co
    #
    cC
    cs1
    #
    cD
    cs1
    #
    cconcat
    co
    #
    wceq
    #
    @9
    @12
    wceq
    @10
    @13
    wceq
    wa
    #
    @6
    @7
    @11
    @8
    @14
    @7
    @11
    wceq
    @6
    cA
    cB
    df-s2
    a1i
    @8
    @14
    wceq
    @6
    cC
    cD
    df-s2
    a1i
    eqeq12d
    @6
    @9
    cV
    cword
    #
    wcel
    #
    @10
    @17
    wcel
    #
    wa
    #
    @12
    @17
    wcel
    #
    @13
    @17
    wcel
    #
    wa
    #
    @9
    chash
    cfv
    #
    @12
    chash
    cfv
    #
    wceq
    #
    @15
    @16
    wb
    @2
    @20
    @5
    @0
    @18
    @1
    @19
    cA
    cV
    s1cl
    cB
    cV
    s1cl
    anim12i
    adantr
    @5
    @23
    @2
    @3
    @21
    @4
    @22
    cC
    cV
    s1cl
    cD
    cV
    s1cl
    anim12i
    adantl
    @26
    @6
    @24
    c1
    @25
    cA
    s1len
    cC
    s1len
    eqtr4i
    a1i
    @9
    @10
    @12
    @13
    cV
    ccatopth
    syl3anc
    bitrd
end
