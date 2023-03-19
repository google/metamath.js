include "c1.mm"
include "cneg.mm"
include "csm.mm"
include "co.mm"
include "cva.mm"
include "cpjh.mm"
include "cfv.mm"
include "cmv.mm"
include "neg1cn.mm"
include "hvmulcli.mm"
include "pjaddii.mm"
include "pjmulii.mm"
include "oveq2i.mm"
include "eqtri.mm"
include "hvsubvali.mm"
include "fveq2i.mm"
include "pjhclii.mm"
include "3eqtr4i.mm"

theorem pjsubii
  let cA: class A
  let cB: class B
  let cH: class H
  assume pjidm.1: |- H e. CH
  assume pjidm.2: |- A e. ~H
  assume pjsub.3: |- B e. ~H


  assert |- ( ( projh ` H ) ` ( A -h B ) ) = ( ( ( projh ` H ) ` A ) -h ( ( projh ` H ) ` B ) )

  proof
    cA
    c1
    cneg
    #
    cB
    csm
    co
    #
    cva
    co
    #
    cH
    cpjh
    cfv
    #
    cfv
    #
    cA
    @3
    cfv
    #
    @0
    cB
    @3
    cfv
    #
    csm
    co
    #
    cva
    co
    #
    cA
    cB
    cmv
    co
    #
    @3
    cfv
    @5
    @6
    cmv
    co
    @4
    @5
    @1
    @3
    cfv
    #
    cva
    co
    @8
    cA
    @1
    cH
    pjidm.1
    pjidm.2
    @0
    cB
    neg1cn
    pjsub.3
    hvmulcli
    pjaddii
    @10
    @7
    @5
    cva
    cB
    @0
    cH
    pjidm.1
    pjsub.3
    neg1cn
    pjmulii
    oveq2i
    eqtri
    @9
    @2
    @3
    cA
    cB
    pjidm.2
    pjsub.3
    hvsubvali
    fveq2i
    @5
    @6
    cA
    cH
    pjidm.1
    pjidm.2
    pjhclii
    cB
    cH
    pjidm.1
    pjsub.3
    pjhclii
    hvsubvali
    3eqtr4i
end
