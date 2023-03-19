include "wcel.mm"
include "w3a.mm"
include "wa.mm"
include "cs3.mm"
include "wceq.mm"
include "cs2.mm"
include "cs1.mm"
include "cconcat.mm"
include "co.mm"
include "df-s3.mm"
include "a1i.mm"
include "eqeq12d.mm"
include "cword.mm"
include "chash.mm"
include "cfv.mm"
include "wb.mm"
include "s2cl.mm"
include "s1cl.mm"
include "anim12i.mm"
include "3impa.mm"
include "adantr.mm"
include "adantl.mm"
include "c2.mm"
include "s2len.mm"
include "eqtr4i.mm"
include "ccatopth.mm"
include "syl3anc.mm"
include "bitrd.mm"

theorem s3eqs2s1eq
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  let cV: class V


  assert |- ( ( ( A e. V /\ B e. V /\ C e. V ) /\ ( D e. V /\ E e. V /\ F e. V ) ) -> ( <" A B C "> = <" D E F "> <-> ( <" A B "> = <" D E "> /\ <" C "> = <" F "> ) ) )

  proof
    cA
    cV
    wcel
    #
    cB
    cV
    wcel
    #
    cC
    cV
    wcel
    #
    w3a
    #
    cD
    cV
    wcel
    #
    cE
    cV
    wcel
    #
    cF
    cV
    wcel
    #
    w3a
    #
    wa
    #
    cA
    cB
    cC
    cs3
    #
    cD
    cE
    cF
    cs3
    #
    wceq
    cA
    cB
    cs2
    #
    cC
    cs1
    #
    cconcat
    co
    #
    cD
    cE
    cs2
    #
    cF
    cs1
    #
    cconcat
    co
    #
    wceq
    #
    @11
    @14
    wceq
    @12
    @15
    wceq
    wa
    #
    @8
    @9
    @13
    @10
    @16
    @9
    @13
    wceq
    @8
    cA
    cB
    cC
    df-s3
    a1i
    @10
    @16
    wceq
    @8
    cD
    cE
    cF
    df-s3
    a1i
    eqeq12d
    @8
    @11
    cV
    cword
    #
    wcel
    #
    @12
    @19
    wcel
    #
    wa
    #
    @14
    @19
    wcel
    #
    @15
    @19
    wcel
    #
    wa
    #
    @11
    chash
    cfv
    #
    @14
    chash
    cfv
    #
    wceq
    #
    @17
    @18
    wb
    @3
    @22
    @7
    @0
    @1
    @2
    @22
    @0
    @1
    wa
    @20
    @2
    @21
    cA
    cB
    cV
    s2cl
    cC
    cV
    s1cl
    anim12i
    3impa
    adantr
    @7
    @25
    @3
    @4
    @5
    @6
    @25
    @4
    @5
    wa
    @23
    @6
    @24
    cD
    cE
    cV
    s2cl
    cF
    cV
    s1cl
    anim12i
    3impa
    adantl
    @28
    @8
    @26
    c2
    @27
    cA
    cB
    s2len
    cD
    cE
    s2len
    eqtr4i
    a1i
    @11
    @12
    @14
    @15
    cV
    ccatopth
    syl3anc
    bitrd
end
