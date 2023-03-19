include "cn.mm"
include "wcel.mm"
include "cgcd.mm"
include "co.mm"
include "c1.mm"
include "wceq.mm"
include "wa.mm"
include "cz.mm"
include "w3a.mm"
include "cdiv.mm"
include "cmul.mm"
include "cmo.mm"
include "wb.mm"
include "simpl.mm"
include "nncn.mm"
include "div1d.mm"
include "oveq2.mm"
include "eqcomd.mm"
include "sylan9req.mm"
include "jca.mm"
include "cncongr.mm"
include "sylan2.mm"

theorem cncongrcoprm
  let cA: class A
  let cB: class B
  let cC: class C
  let cN: class N


  assert |- ( ( ( A e. ZZ /\ B e. ZZ /\ C e. ZZ ) /\ ( N e. NN /\ ( C gcd N ) = 1 ) ) -> ( ( ( A x. C ) mod N ) = ( ( B x. C ) mod N ) <-> ( A mod N ) = ( B mod N ) ) )

  proof
    cN
    cn
    wcel
    #
    cC
    cN
    cgcd
    co
    #
    c1
    wceq
    #
    wa
    #
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
    @0
    cN
    cN
    @1
    cdiv
    co
    #
    wceq
    #
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
    cN
    cmo
    co
    cB
    cN
    cmo
    co
    wceq
    wb
    @3
    @0
    @5
    @0
    @2
    simpl
    @0
    @2
    cN
    cN
    c1
    cdiv
    co
    #
    @4
    @0
    cN
    cN
    nncn
    div1d
    @2
    @4
    @6
    @1
    c1
    cN
    cdiv
    oveq2
    eqcomd
    sylan9req
    jca
    cA
    cB
    cC
    cN
    cN
    cncongr
    sylan2
end
