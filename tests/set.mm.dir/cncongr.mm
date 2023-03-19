include "cz.mm"
include "wcel.mm"
include "w3a.mm"
include "cn.mm"
include "cgcd.mm"
include "co.mm"
include "cdiv.mm"
include "wceq.mm"
include "wa.mm"
include "cmul.mm"
include "cmo.mm"
include "cncongr1.mm"
include "cncongr2.mm"
include "impbid.mm"

theorem cncongr
  let cA: class A
  let cB: class B
  let cC: class C
  let cM: class M
  let cN: class N


  assert |- ( ( ( A e. ZZ /\ B e. ZZ /\ C e. ZZ ) /\ ( N e. NN /\ M = ( N / ( C gcd N ) ) ) ) -> ( ( ( A x. C ) mod N ) = ( ( B x. C ) mod N ) <-> ( A mod M ) = ( B mod M ) ) )

  proof
    cA
    cz
    wcel
    cB
    cz
    wcel
    cC
    cz
    wcel
    w3a
    cN
    cn
    wcel
    cM
    cN
    cC
    cN
    cgcd
    co
    cdiv
    co
    wceq
    wa
    wa
    cA
    cC
    cmul
    co
    cN
    cmo
    co
    cB
    cC
    cmul
    co
    cN
    cmo
    co
    wceq
    cA
    cM
    cmo
    co
    cB
    cM
    cmo
    co
    wceq
    cA
    cB
    cC
    cM
    cN
    cncongr1
    cA
    cB
    cC
    cM
    cN
    cncongr2
    impbid
end
