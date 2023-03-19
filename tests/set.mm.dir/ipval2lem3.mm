include "cnv.mm"
include "wcel.mm"
include "w3a.mm"
include "c1.mm"
include "co.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "cr.mm"
include "wceq.mm"
include "wa.mm"
include "nvsid.mm"
include "oveq2d.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "3adant2.mm"
include "cc.mm"
include "ax-1cn.mm"
include "ipval2lem2.mm"
include "mpan2.mm"
include "eqeltrrd.mm"

theorem ipval2lem3
  let cA: class A
  let cB: class B
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


  assert |- ( ( U e. NrmCVec /\ A e. X /\ B e. X ) -> ( ( N ` ( A G B ) ) ^ 2 ) e. RR )

  proof
    cU
    cnv
    wcel
    #
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    w3a
    #
    cA
    c1
    cB
    cS
    co
    #
    cG
    co
    #
    cN
    cfv
    #
    c2
    cexp
    co
    #
    cA
    cB
    cG
    co
    #
    cN
    cfv
    #
    c2
    cexp
    co
    #
    cr
    @0
    @2
    @7
    @10
    wceq
    @1
    @0
    @2
    wa
    #
    @6
    @9
    c2
    cexp
    @11
    @5
    @8
    cN
    @11
    @4
    cB
    cA
    cG
    cB
    cS
    cU
    cX
    dipfval.1
    dipfval.4
    nvsid
    oveq2d
    fveq2d
    oveq1d
    3adant2
    @3
    c1
    cc
    wcel
    @7
    cr
    wcel
    ax-1cn
    cA
    cB
    c1
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
    mpan2
    eqeltrrd
end
