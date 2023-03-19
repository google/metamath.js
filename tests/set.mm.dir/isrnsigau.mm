include "csiga.mm"
include "crn.mm"
include "cuni.mm"
include "wcel.mm"
include "cfv.mm"
include "cpw.mm"
include "wss.mm"
include "cv.mm"
include "cdif.mm"
include "wral.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wi.mm"
include "w3a.mm"
include "wa.mm"
include "sgon.mm"
include "cvv.mm"
include "wb.mm"
include "elex.mm"
include "issiga.mm"
include "syl.mm"
include "mpbid.mm"

theorem isrnsigau
  let vx: setvar x
  let cS: class S

  disjoint S x
  assert |- ( S e. U. ran sigAlgebra -> ( S C_ ~P U. S /\ ( U. S e. S /\ A. x e. S ( U. S \ x ) e. S /\ A. x e. ~P S ( x ~<_ _om -> U. x e. S ) ) ) )

  proof
    cS
    csiga
    crn
    cuni
    #
    wcel
    #
    cS
    cS
    cuni
    #
    csiga
    cfv
    wcel
    #
    cS
    @2
    cpw
    wss
    @2
    cS
    wcel
    @2
    vx
    cv
    #
    cdif
    cS
    wcel
    vx
    cS
    wral
    @4
    com
    cdom
    wbr
    @4
    cuni
    cS
    wcel
    wi
    vx
    cS
    cpw
    wral
    w3a
    wa
    #
    cS
    sgon
    @1
    cS
    cvv
    wcel
    @3
    @5
    wb
    cS
    @0
    elex
    vx
    cS
    @2
    issiga
    syl
    mpbid
end
