include "cfn.mm"
include "wcel.mm"
include "cmap.mm"
include "co.mm"
include "wss.mm"
include "mapfi.mm"
include "anidms.mm"
include "cv.mm"
include "wf.mm"
include "cab.mm"
include "wf1o.mm"
include "symgbas.mm"
include "f1of.mm"
include "ss2abi.mm"
include "eqsstri.mm"
include "wceq.mm"
include "mapvalg.mm"
include "syl5sseqr.mm"
include "ssfi.mm"
include "syl2anc.mm"

theorem symgbasfi
  let cA: class A
  let cB: class B
  let cG: class G
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let cF: class F
  let cV: class V
  assume symgbas.1: |- G = ( SymGrp ` A )
  assume symgbas.2: |- B = ( Base ` G )


  assert |- ( A e. Fin -> B e. Fin )

  proof
    cA
    cfn
    wcel
    #
    cA
    cA
    cmap
    co
    #
    cfn
    wcel
    #
    cB
    @1
    wss
    cB
    cfn
    wcel
    @0
    @2
    cA
    cA
    mapfi
    anidms
    @0
    cA
    cA
    vf
    cv
    #
    wf
    #
    vf
    cab
    #
    cB
    @1
    cB
    cA
    cA
    @3
    wf1o
    #
    vf
    cab
    @5
    vf
    cA
    cB
    cG
    symgbas.1
    symgbas.2
    symgbas
    @6
    @4
    vf
    cA
    cA
    @3
    f1of
    ss2abi
    eqsstri
    @0
    @1
    @5
    wceq
    cA
    cA
    cfn
    cfn
    vf
    mapvalg
    anidms
    syl5sseqr
    @1
    cB
    ssfi
    syl2anc
end
