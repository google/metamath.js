include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "cxp.mm"
include "cres.mm"
include "cin.mm"
include "cxr.mm"
include "wf.mm"
include "cdm.mm"
include "wceq.mm"
include "xmetf.mm"
include "fdm.mm"
include "metreslem.mm"
include "3syl.mm"
include "wss.mm"
include "inss1.mm"
include "xmetres2.mm"
include "mpan2.mm"
include "eqeltrd.mm"

theorem xmetres
  let cD: class D
  let cR: class R
  let cX: class X


  assert |- ( D e. ( *Met ` X ) -> ( D |` ( R X. R ) ) e. ( *Met ` ( X i^i R ) ) )

  proof
    cD
    cX
    cxmt
    cfv
    wcel
    #
    cD
    cR
    cR
    cxp
    cres
    #
    cD
    cX
    cR
    cin
    #
    @2
    cxp
    cres
    #
    @2
    cxmt
    cfv
    #
    @0
    cX
    cX
    cxp
    #
    cxr
    cD
    wf
    cD
    cdm
    @5
    wceq
    @1
    @3
    wceq
    cD
    cX
    xmetf
    @5
    cxr
    cD
    fdm
    cD
    cR
    cX
    metreslem
    3syl
    @0
    @2
    cX
    wss
    @3
    @4
    wcel
    cX
    cR
    inss1
    cD
    @2
    cX
    xmetres2
    mpan2
    eqeltrd
end
