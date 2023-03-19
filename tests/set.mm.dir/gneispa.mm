include "ctop.mm"
include "wcel.mm"
include "cv.mm"
include "csn.mm"
include "cnei.mm"
include "cfv.mm"
include "c0.mm"
include "wne.mm"
include "wel.mm"
include "wral.mm"
include "wa.mm"
include "wss.mm"
include "snssi.mm"
include "tpnei.mm"
include "syl5ib.mm"
include "imp.mm"
include "ne0i.mm"
include "syl.mm"
include "elnei.mm"
include "3expia.mm"
include "ralrimiv.mm"
include "jca.mm"
include "ex.mm"

theorem gneispa
  let vn: setvar n
  let cJ: class J
  let cX: class X
  let vp: setvar p
  assume gneispace.x: |- X = U. J

  disjoint J n
  disjoint J p
  disjoint n p
  disjoint X n
  assert |- ( J e. Top -> A. p e. X ( ( ( nei ` J ) ` { p } ) =/= (/) /\ A. n e. ( ( nei ` J ) ` { p } ) p e. n ) )

  proof
    cJ
    ctop
    wcel
    #
    vp
    cv
    #
    csn
    #
    cJ
    cnei
    cfv
    cfv
    #
    c0
    wne
    #
    vp
    vn
    wel
    #
    vn
    @3
    wral
    #
    wa
    #
    vp
    cX
    @0
    @1
    cX
    wcel
    #
    @7
    @0
    @8
    wa
    #
    @4
    @6
    @9
    cX
    @3
    wcel
    #
    @4
    @0
    @8
    @10
    @8
    @2
    cX
    wss
    @0
    @10
    @1
    cX
    snssi
    @2
    cJ
    cX
    gneispace.x
    tpnei
    syl5ib
    imp
    @3
    cX
    ne0i
    syl
    @9
    @5
    vn
    @3
    @0
    @8
    vn
    cv
    #
    @3
    wcel
    @5
    cX
    @1
    cJ
    @11
    elnei
    3expia
    ralrimiv
    jca
    ex
    ralrimiv
end
