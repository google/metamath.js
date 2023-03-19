include "csubgr.mm"
include "wbr.mm"
include "wss.mm"
include "cdm.mm"
include "cres.mm"
include "wceq.mm"
include "cpw.mm"
include "w3a.mm"
include "subgrprop.mm"
include "resss.mm"
include "sseq1.mm"
include "mpbiri.mm"
include "3anim2i.mm"
include "syl.mm"

theorem subgrprop2
  let cA: class A
  let cB: class B
  let cS: class S
  let cE: class E
  let cG: class G
  let cI: class I
  let cV: class V
  let vs: setvar s
  let vg: setvar g
  assume issubgr.v: |- V = ( Vtx ` S )
  assume issubgr.a: |- A = ( Vtx ` G )
  assume issubgr.i: |- I = ( iEdg ` S )
  assume issubgr.b: |- B = ( iEdg ` G )
  assume issubgr.e: |- E = ( Edg ` S )


  assert |- ( S SubGraph G -> ( V C_ A /\ I C_ B /\ E C_ ~P V ) )

  proof
    cS
    cG
    csubgr
    wbr
    cV
    cA
    wss
    #
    cI
    cB
    cI
    cdm
    #
    cres
    #
    wceq
    #
    cE
    cV
    cpw
    wss
    #
    w3a
    @0
    cI
    cB
    wss
    #
    @4
    w3a
    cA
    cB
    cS
    cE
    cG
    cI
    cV
    issubgr.v
    issubgr.a
    issubgr.i
    issubgr.b
    issubgr.e
    subgrprop
    @3
    @5
    @0
    @4
    @3
    @5
    @2
    cB
    wss
    cB
    @1
    resss
    cI
    @2
    cB
    sseq1
    mpbiri
    3anim2i
    syl
end
