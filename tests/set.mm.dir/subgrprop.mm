include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "csubgr.mm"
include "wbr.mm"
include "wss.mm"
include "cdm.mm"
include "cres.mm"
include "wceq.mm"
include "cpw.mm"
include "w3a.mm"
include "subgrv.mm"
include "wi.mm"
include "issubgr.mm"
include "biimpd.mm"
include "ancoms.mm"
include "mpcom.mm"

theorem subgrprop
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


  assert |- ( S SubGraph G -> ( V C_ A /\ I = ( B |` dom I ) /\ E C_ ~P V ) )

  proof
    cS
    cvv
    wcel
    #
    cG
    cvv
    wcel
    #
    wa
    cS
    cG
    csubgr
    wbr
    #
    cV
    cA
    wss
    cI
    cB
    cI
    cdm
    cres
    wceq
    cE
    cV
    cpw
    wss
    w3a
    #
    cS
    cG
    subgrv
    @1
    @0
    @2
    @3
    wi
    @1
    @0
    wa
    @2
    @3
    cA
    cB
    cS
    cvv
    cE
    cG
    cI
    cV
    cvv
    issubgr.v
    issubgr.a
    issubgr.i
    issubgr.b
    issubgr.e
    issubgr
    biimpd
    ancoms
    mpcom
end
