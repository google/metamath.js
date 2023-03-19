include "wfun.mm"
include "cfn.mm"
include "wcel.mm"
include "wa.mm"
include "cima.mm"
include "cres.mm"
include "cdm.mm"
include "imadmres.mm"
include "wfo.mm"
include "wss.mm"
include "simpr.mm"
include "cin.mm"
include "dmres.mm"
include "inss1.mm"
include "eqsstri.mm"
include "ssfi.mm"
include "sylancl.mm"
include "resss.mm"
include "dmss.mm"
include "mp1i.mm"
include "fores.mm"
include "syldan.mm"
include "fofi.mm"
include "syl2anc.mm"
include "syl5eqelr.mm"

theorem imafi
  let cF: class F
  let cX: class X


  assert |- ( ( Fun F /\ X e. Fin ) -> ( F " X ) e. Fin )

  proof
    cF
    wfun
    #
    cX
    cfn
    wcel
    #
    wa
    #
    cF
    cX
    cima
    cF
    cF
    cX
    cres
    #
    cdm
    #
    cima
    #
    cfn
    cF
    cX
    imadmres
    @2
    @4
    cfn
    wcel
    #
    @4
    @5
    cF
    @4
    cres
    #
    wfo
    #
    @5
    cfn
    wcel
    @2
    @1
    @4
    cX
    wss
    @6
    @0
    @1
    simpr
    @4
    cX
    cF
    cdm
    #
    cin
    cX
    cF
    cX
    dmres
    cX
    @9
    inss1
    eqsstri
    cX
    @4
    ssfi
    sylancl
    @0
    @1
    @4
    @9
    wss
    #
    @8
    @3
    cF
    wss
    @10
    @2
    cF
    cX
    resss
    @3
    cF
    dmss
    mp1i
    @4
    cF
    fores
    syldan
    @4
    @5
    @7
    fofi
    syl2anc
    syl5eqelr
end
