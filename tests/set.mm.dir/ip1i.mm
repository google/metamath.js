include "c1.mm"
include "cnmcv.mm"
include "cfv.mm"
include "eqid.mm"
include "ax-1cn.mm"
include "ip1ilem.mm"

theorem ip1i
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let cS: class S
  let cU: class U
  let cG: class G
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let cN: class N
  assume ip1i.1: |- X = ( BaseSet ` U )
  assume ip1i.2: |- G = ( +v ` U )
  assume ip1i.4: |- S = ( .sOLD ` U )
  assume ip1i.7: |- P = ( .iOLD ` U )
  assume ip1i.9: |- U e. CPreHilOLD
  assume ip1i.a: |- A e. X
  assume ip1i.b: |- B e. X
  assume ip1i.c: |- C e. X


  assert |- ( ( ( A G B ) P C ) + ( ( A G ( -u 1 S B ) ) P C ) ) = ( 2 x. ( A P C ) )

  proof
    cA
    cB
    cC
    cP
    cS
    cU
    cG
    c1
    cU
    cnmcv
    cfv
    #
    cX
    ip1i.1
    ip1i.2
    ip1i.4
    ip1i.7
    ip1i.9
    ip1i.a
    ip1i.b
    ip1i.c
    @0
    eqid
    ax-1cn
    ip1ilem
end
