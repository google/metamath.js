include "cnv.mm"
include "wcel.mm"
include "w3a.mm"
include "cc.mm"
include "wa.mm"
include "co.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "ipval2lem2.mm"
include "recnd.mm"

theorem ipval2lem4
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cS: class S
  let cU: class U
  let cG: class G
  let cN: class N
  let cX: class X
  let vk: setvar k
  let vu: setvar u
  let vx: setvar x
  let vy: setvar y
  assume dipfval.1: |- X = ( BaseSet ` U )
  assume dipfval.2: |- G = ( +v ` U )
  assume dipfval.4: |- S = ( .sOLD ` U )
  assume dipfval.6: |- N = ( normCV ` U )
  assume dipfval.7: |- P = ( .iOLD ` U )


  assert |- ( ( ( U e. NrmCVec /\ A e. X /\ B e. X ) /\ C e. CC ) -> ( ( N ` ( A G ( C S B ) ) ) ^ 2 ) e. CC )

  proof
    cU
    cnv
    wcel
    cA
    cX
    wcel
    cB
    cX
    wcel
    w3a
    cC
    cc
    wcel
    wa
    cA
    cC
    cB
    cS
    co
    cG
    co
    cN
    cfv
    c2
    cexp
    co
    cA
    cB
    cC
    cP
    cS
    cU
    cG
    cN
    cX
    dipfval.1
    dipfval.2
    dipfval.4
    dipfval.6
    dipfval.7
    ipval2lem2
    recnd
end
