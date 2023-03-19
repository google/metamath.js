include "cz.mm"
include "wcel.mm"
include "cn0.mm"
include "cr.mm"
include "cneg.mm"
include "cn.mm"
include "wa.mm"
include "wo.mm"
include "co.mm"
include "cmul.mm"
include "wceq.mm"
include "elznn0nn.mm"
include "ipasslem1.mm"
include "nnnn0.mm"
include "ipasslem2.mm"
include "sylan.mm"
include "adantll.mm"
include "recn.mm"
include "negnegd.mm"
include "oveq1d.mm"
include "ad2antrr.mm"
include "3eqtr3d.mm"
include "jaoian.mm"
include "sylanb.mm"

theorem ipasslem3
  let cA: class A
  let cB: class B
  let cP: class P
  let cS: class S
  let cU: class U
  let cG: class G
  let cN: class N
  let cX: class X
  let vj: setvar j
  let vk: setvar k
  let cC: class C
  let vx: setvar x
  let vy: setvar y
  assume ip1i.1: |- X = ( BaseSet ` U )
  assume ip1i.2: |- G = ( +v ` U )
  assume ip1i.4: |- S = ( .sOLD ` U )
  assume ip1i.7: |- P = ( .iOLD ` U )
  assume ip1i.9: |- U e. CPreHilOLD
  assume ipasslem1.b: |- B e. X


  assert |- ( ( N e. ZZ /\ A e. X ) -> ( ( N S A ) P B ) = ( N x. ( A P B ) ) )

  proof
    cN
    cz
    wcel
    cN
    cn0
    wcel
    #
    cN
    cr
    wcel
    #
    cN
    cneg
    #
    cn
    wcel
    #
    wa
    #
    wo
    cA
    cX
    wcel
    #
    cN
    cA
    cS
    co
    #
    cB
    cP
    co
    #
    cN
    cA
    cB
    cP
    co
    #
    cmul
    co
    #
    wceq
    #
    cN
    elznn0nn
    @0
    @5
    @10
    @4
    cA
    cB
    cP
    cS
    cU
    cG
    cN
    cX
    ip1i.1
    ip1i.2
    ip1i.4
    ip1i.7
    ip1i.9
    ipasslem1.b
    ipasslem1
    @4
    @5
    wa
    @2
    cneg
    #
    cA
    cS
    co
    #
    cB
    cP
    co
    #
    @11
    @8
    cmul
    co
    #
    @7
    @9
    @3
    @5
    @13
    @14
    wceq
    #
    @1
    @3
    @2
    cn0
    wcel
    @5
    @15
    @2
    nnnn0
    cA
    cB
    cP
    cS
    cU
    cG
    @2
    cX
    ip1i.1
    ip1i.2
    ip1i.4
    ip1i.7
    ip1i.9
    ipasslem1.b
    ipasslem2
    sylan
    adantll
    @1
    @13
    @7
    wceq
    @3
    @5
    @1
    @12
    @6
    cB
    cP
    @1
    @11
    cN
    cA
    cS
    @1
    cN
    cN
    recn
    negnegd
    #
    oveq1d
    oveq1d
    ad2antrr
    @1
    @14
    @9
    wceq
    @3
    @5
    @1
    @11
    cN
    @8
    cmul
    @16
    oveq1d
    ad2antrr
    3eqtr3d
    jaoian
    sylanb
end
