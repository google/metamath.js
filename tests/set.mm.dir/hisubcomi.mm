include "c1.mm"
include "cneg.mm"
include "cmv.mm"
include "co.mm"
include "csm.mm"
include "csp.mm"
include "hvnegdii.mm"
include "oveq12i.mm"
include "ccj.mm"
include "cfv.mm"
include "cmul.mm"
include "neg1cn.mm"
include "hvsubcli.mm"
include "his35i.mm"
include "cr.mm"
include "wcel.mm"
include "wceq.mm"
include "neg1rr.mm"
include "cjre.mm"
include "ax-mp.mm"
include "oveq2i.mm"
include "ax-1cn.mm"
include "mul2negi.mm"
include "1t1e1.mm"
include "3eqtri.mm"
include "oveq1i.mm"
include "hicli.mm"
include "mulid2i.mm"
include "eqtr3i.mm"

theorem hisubcomi
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume hisubcom.1: |- A e. ~H
  assume hisubcom.2: |- B e. ~H
  assume hisubcom.3: |- C e. ~H
  assume hisubcom.4: |- D e. ~H


  assert |- ( ( A -h B ) .ih ( C -h D ) ) = ( ( B -h A ) .ih ( D -h C ) )

  proof
    c1
    cneg
    #
    cB
    cA
    cmv
    co
    #
    csm
    co
    #
    @0
    cD
    cC
    cmv
    co
    #
    csm
    co
    #
    csp
    co
    #
    cA
    cB
    cmv
    co
    #
    cC
    cD
    cmv
    co
    #
    csp
    co
    @1
    @3
    csp
    co
    #
    @2
    @6
    @4
    @7
    csp
    cB
    cA
    hisubcom.2
    hisubcom.1
    hvnegdii
    cD
    cC
    hisubcom.4
    hisubcom.3
    hvnegdii
    oveq12i
    @5
    @0
    @0
    ccj
    cfv
    #
    cmul
    co
    #
    @8
    cmul
    co
    c1
    @8
    cmul
    co
    @8
    @0
    @0
    @1
    @3
    neg1cn
    neg1cn
    cB
    cA
    hisubcom.2
    hisubcom.1
    hvsubcli
    #
    cD
    cC
    hisubcom.4
    hisubcom.3
    hvsubcli
    #
    his35i
    @10
    c1
    @8
    cmul
    @10
    @0
    @0
    cmul
    co
    c1
    c1
    cmul
    co
    c1
    @9
    @0
    @0
    cmul
    @0
    cr
    wcel
    @9
    @0
    wceq
    neg1rr
    @0
    cjre
    ax-mp
    oveq2i
    c1
    c1
    ax-1cn
    ax-1cn
    mul2negi
    1t1e1
    3eqtri
    oveq1i
    @8
    @1
    @3
    @11
    @12
    hicli
    mulid2i
    3eqtri
    eqtr3i
end
