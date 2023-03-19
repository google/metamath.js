include "wcel.mm"
include "wfun.mm"
include "w3a.mm"
include "csubgr.mm"
include "wbr.mm"
include "wss.mm"
include "cdm.mm"
include "cres.mm"
include "wceq.mm"
include "cpw.mm"
include "wb.mm"
include "issubgr.mm"
include "3adant2.mm"
include "resss.mm"
include "sseq1.mm"
include "mpbiri.mm"
include "wi.mm"
include "wa.mm"
include "funssres.mm"
include "eqcomd.mm"
include "ex.mm"
include "3ad2ant2.mm"
include "impbid2.mm"
include "3anbi2d.mm"
include "bitrd.mm"

theorem issubgr2
  let cA: class A
  let cB: class B
  let cS: class S
  let cU: class U
  let cE: class E
  let cG: class G
  let cI: class I
  let cV: class V
  let cW: class W
  let vs: setvar s
  let vg: setvar g
  assume issubgr.v: |- V = ( Vtx ` S )
  assume issubgr.a: |- A = ( Vtx ` G )
  assume issubgr.i: |- I = ( iEdg ` S )
  assume issubgr.b: |- B = ( iEdg ` G )
  assume issubgr.e: |- E = ( Edg ` S )


  assert |- ( ( G e. W /\ Fun B /\ S e. U ) -> ( S SubGraph G <-> ( V C_ A /\ I C_ B /\ E C_ ~P V ) ) )

  proof
    cG
    cW
    wcel
    #
    cB
    wfun
    #
    cS
    cU
    wcel
    #
    w3a
    #
    cS
    cG
    csubgr
    wbr
    #
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
    #
    @5
    cI
    cB
    wss
    #
    @9
    w3a
    @0
    @2
    @4
    @10
    wb
    @1
    cA
    cB
    cS
    cU
    cE
    cG
    cI
    cV
    cW
    issubgr.v
    issubgr.a
    issubgr.i
    issubgr.b
    issubgr.e
    issubgr
    3adant2
    @3
    @8
    @11
    @5
    @9
    @3
    @8
    @11
    @8
    @11
    @7
    cB
    wss
    cB
    @6
    resss
    cI
    @7
    cB
    sseq1
    mpbiri
    @1
    @0
    @11
    @8
    wi
    @2
    @1
    @11
    @8
    @1
    @11
    wa
    @7
    cI
    cB
    cI
    funssres
    eqcomd
    ex
    3ad2ant2
    impbid2
    3anbi2d
    bitrd
end
