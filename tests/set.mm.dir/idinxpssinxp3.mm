include "cid.mm"
include "cxp.mm"
include "cin.mm"
include "wss.mm"
include "cv.mm"
include "wbr.mm"
include "wral.mm"
include "cres.mm"
include "idinxpssinxp2.mm"
include "issref.mm"
include "bitr4i.mm"

theorem idinxpssinxp3
  let cA: class A
  let cR: class R
  let vx: setvar x


  assert |- ( ( _I i^i ( A X. A ) ) C_ ( R i^i ( A X. A ) ) <-> ( _I |` A ) C_ R )

  proof
    cid
    cA
    cA
    cxp
    #
    cin
    cR
    @0
    cin
    wss
    vx
    cv
    #
    @1
    cR
    wbr
    vx
    cA
    wral
    cid
    cA
    cres
    cR
    wss
    vx
    cA
    cR
    idinxpssinxp2
    vx
    cA
    cR
    issref
    bitr4i
end
