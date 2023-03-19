include "cme.mm"
include "cfv.mm"
include "wcel.mm"
include "cxp.mm"
include "cres.mm"
include "cin.mm"
include "cr.mm"
include "wf.mm"
include "cdm.mm"
include "wceq.mm"
include "metf.mm"
include "fdm.mm"
include "metreslem.mm"
include "3syl.mm"
include "wss.mm"
include "inss1.mm"
include "metres2.mm"
include "mpan2.mm"
include "eqeltrd.mm"

theorem metres
  let cD: class D
  let cR: class R
  let cX: class X


  assert |- ( D e. ( Met ` X ) -> ( D |` ( R X. R ) ) e. ( Met ` ( X i^i R ) ) )

  proof
    cD
    cX
    cme
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
    cme
    cfv
    #
    @0
    cX
    cX
    cxp
    #
    cr
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
    metf
    @5
    cr
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
    metres2
    mpan2
    eqeltrd
end
