include "ccrd.mm"
include "cdm.mm"
include "wcel.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "cfn.mm"
include "wn.mm"
include "csdm.mm"
include "wb.mm"
include "con0.mm"
include "omelon.mm"
include "onenon.mm"
include "ax-mp.mm"
include "domtri2.mm"
include "mpan.mm"
include "isfinite.mm"
include "notbii.mm"
include "syl6bbr.mm"
include "biimpar.mm"

theorem numinfctb
  let cS: class S


  assert |- ( ( S e. dom card /\ -. S e. Fin ) -> _om ~<_ S )

  proof
    cS
    ccrd
    cdm
    #
    wcel
    #
    com
    cS
    cdom
    wbr
    #
    cS
    cfn
    wcel
    #
    wn
    #
    @1
    @2
    cS
    com
    csdm
    wbr
    #
    wn
    #
    @4
    com
    @0
    wcel
    #
    @1
    @2
    @6
    wb
    com
    con0
    wcel
    @7
    omelon
    com
    onenon
    ax-mp
    com
    cS
    domtri2
    mpan
    @3
    @5
    cS
    isfinite
    notbii
    syl6bbr
    biimpar
end
