include "csubgr.mm"
include "wbr.mm"
include "wss.mm"
include "ciedg.mm"
include "cfv.mm"
include "wa.mm"
include "cpw.mm"
include "w3a.mm"
include "eqid.mm"
include "subgrprop2.mm"
include "3simpa.mm"
include "syl.mm"
include "simprl.mm"
include "crn.mm"
include "rnss.mm"
include "ad2antll.mm"
include "wb.mm"
include "cvv.mm"
include "wcel.mm"
include "subgrv.mm"
include "cedg.mm"
include "wceq.mm"
include "edgval.mm"
include "a1i.mm"
include "syl5eq.mm"
include "sseq12d.mm"
include "adantr.mm"
include "mpbird.mm"
include "jca.mm"
include "mpdan.mm"

theorem subgrprop3
  let cA: class A
  let cB: class B
  let cS: class S
  let cE: class E
  let cG: class G
  let cV: class V
  assume subgrprop3.v: |- V = ( Vtx ` S )
  assume subgrprop3.a: |- A = ( Vtx ` G )
  assume subgrprop3.e: |- E = ( Edg ` S )
  assume subgrprop3.b: |- B = ( Edg ` G )


  assert |- ( S SubGraph G -> ( V C_ A /\ E C_ B ) )

  proof
    cS
    cG
    csubgr
    wbr
    #
    cV
    cA
    wss
    #
    cS
    ciedg
    cfv
    #
    cG
    ciedg
    cfv
    #
    wss
    #
    wa
    #
    @1
    cE
    cB
    wss
    #
    wa
    @0
    @1
    @4
    cE
    cV
    cpw
    wss
    #
    w3a
    @5
    cA
    @3
    cS
    cE
    cG
    @2
    cV
    subgrprop3.v
    subgrprop3.a
    @2
    eqid
    @3
    eqid
    subgrprop3.e
    subgrprop2
    @1
    @4
    @7
    3simpa
    syl
    @0
    @5
    wa
    #
    @1
    @6
    @0
    @1
    @4
    simprl
    @8
    @6
    @2
    crn
    #
    @3
    crn
    #
    wss
    #
    @4
    @11
    @0
    @1
    @2
    @3
    rnss
    ad2antll
    @0
    @6
    @11
    wb
    #
    @5
    @0
    cS
    cvv
    wcel
    cG
    cvv
    wcel
    wa
    #
    @12
    cS
    cG
    subgrv
    @13
    cE
    @9
    cB
    @10
    @13
    cE
    cS
    cedg
    cfv
    #
    @9
    subgrprop3.e
    @14
    @9
    wceq
    @13
    cS
    edgval
    a1i
    syl5eq
    @13
    cB
    cG
    cedg
    cfv
    #
    @10
    subgrprop3.b
    @15
    @10
    wceq
    @13
    cG
    edgval
    a1i
    syl5eq
    sseq12d
    syl
    adantr
    mpbird
    jca
    mpdan
end
