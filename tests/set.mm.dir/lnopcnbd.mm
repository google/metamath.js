include "clo.mm"
include "wcel.mm"
include "ccop.mm"
include "cbo.mm"
include "cnop.mm"
include "cfv.mm"
include "cr.mm"
include "nmcopex.mm"
include "ex.mm"
include "elbdop2.mm"
include "baibr.mm"
include "sylibd.mm"
include "cv.mm"
include "cno.mm"
include "cmul.mm"
include "co.mm"
include "cle.mm"
include "wbr.mm"
include "chil.mm"
include "wral.mm"
include "wrex.mm"
include "nmopre.mm"
include "nmbdoplb.mm"
include "ralrimiva.mm"
include "wceq.mm"
include "oveq1.mm"
include "breq2d.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "lnopcon.mm"
include "syl5ibr.mm"
include "impbid.mm"

theorem lnopcnbd
  let cT: class T
  let vx: setvar x
  let vy: setvar y


  assert |- ( T e. LinOp -> ( T e. ContOp <-> T e. BndLinOp ) )

  proof
    cT
    clo
    wcel
    #
    cT
    ccop
    wcel
    #
    cT
    cbo
    wcel
    #
    @0
    @1
    cT
    cnop
    cfv
    #
    cr
    wcel
    #
    @2
    @0
    @1
    @4
    cT
    nmcopex
    ex
    @2
    @0
    @4
    cT
    elbdop2
    baibr
    sylibd
    @2
    @1
    @0
    vy
    cv
    #
    cT
    cfv
    cno
    cfv
    #
    vx
    cv
    #
    @5
    cno
    cfv
    #
    cmul
    co
    #
    cle
    wbr
    #
    vy
    chil
    wral
    #
    vx
    cr
    wrex
    #
    @2
    @4
    @6
    @3
    @8
    cmul
    co
    #
    cle
    wbr
    #
    vy
    chil
    wral
    #
    @12
    cT
    nmopre
    @2
    @14
    vy
    chil
    @5
    cT
    nmbdoplb
    ralrimiva
    @11
    @15
    vx
    @3
    cr
    @7
    @3
    wceq
    #
    @10
    @14
    vy
    chil
    @16
    @9
    @13
    @6
    cle
    @7
    @3
    @8
    cmul
    oveq1
    breq2d
    ralbidv
    rspcev
    syl2anc
    vx
    vy
    cT
    lnopcon
    syl5ibr
    impbid
end
