include "wcel.mm"
include "cinftm.mm"
include "cfv.mm"
include "cv.mm"
include "wa.mm"
include "c0g.mm"
include "cplt.mm"
include "wbr.mm"
include "cmg.mm"
include "co.mm"
include "cn.mm"
include "wral.mm"
include "copab.mm"
include "cxp.mm"
include "cvv.mm"
include "wceq.mm"
include "elex.mm"
include "cbs.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "eleq2d.mm"
include "anbi12d.mm"
include "eqidd.mm"
include "breq123d.mm"
include "oveqd.mm"
include "ralbidv.mm"
include "opabbidv.mm"
include "df-inftm.mm"
include "fvex.mm"
include "eqeltri.mm"
include "xpex.mm"
include "opabssxp.mm"
include "ssexi.mm"
include "fvmpt.mm"
include "syl.mm"
include "syl6eqss.mm"

theorem inftmrel
  let cB: class B
  let cV: class V
  let cW: class W
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vn: setvar n
  let cX: class X
  let cY: class Y
  let c.lt: class .<
  let c.x: class .x.
  let c.0: class .0.
  assume inftm.b: |- B = ( Base ` W )


  assert |- ( W e. V -> ( <<< ` W ) C_ ( B X. B ) )

  proof
    cW
    cV
    wcel
    #
    cW
    cinftm
    cfv
    #
    vx
    cv
    #
    cB
    wcel
    #
    vy
    cv
    #
    cB
    wcel
    #
    wa
    #
    cW
    c0g
    cfv
    #
    @2
    cW
    cplt
    cfv
    #
    wbr
    #
    vn
    cv
    #
    @2
    cW
    cmg
    cfv
    #
    co
    #
    @4
    @8
    wbr
    #
    vn
    cn
    wral
    #
    wa
    #
    wa
    #
    vx
    vy
    copab
    #
    cB
    cB
    cxp
    #
    @0
    cW
    cvv
    wcel
    @1
    @17
    wceq
    cW
    cV
    elex
    vw
    cW
    @2
    vw
    cv
    #
    cbs
    cfv
    #
    wcel
    #
    @4
    @20
    wcel
    #
    wa
    #
    @19
    c0g
    cfv
    #
    @2
    @19
    cplt
    cfv
    #
    wbr
    #
    @10
    @2
    @19
    cmg
    cfv
    #
    co
    #
    @4
    @25
    wbr
    #
    vn
    cn
    wral
    #
    wa
    #
    wa
    #
    vx
    vy
    copab
    @17
    cvv
    cinftm
    @19
    cW
    wceq
    #
    @32
    @16
    vx
    vy
    @33
    @23
    @6
    @31
    @15
    @33
    @21
    @3
    @22
    @5
    @33
    @20
    cB
    @2
    @33
    @20
    cW
    cbs
    cfv
    #
    cB
    @19
    cW
    cbs
    fveq2
    inftm.b
    syl6eqr
    #
    eleq2d
    @33
    @20
    cB
    @4
    @35
    eleq2d
    anbi12d
    @33
    @26
    @9
    @30
    @14
    @33
    @24
    @7
    @2
    @2
    @25
    @8
    @19
    cW
    c0g
    fveq2
    @19
    cW
    cplt
    fveq2
    #
    @33
    @2
    eqidd
    breq123d
    @33
    @29
    @13
    vn
    cn
    @33
    @28
    @12
    @4
    @4
    @25
    @8
    @33
    @27
    @11
    @10
    @2
    @19
    cW
    cmg
    fveq2
    oveqd
    @36
    @33
    @4
    eqidd
    breq123d
    ralbidv
    anbi12d
    anbi12d
    opabbidv
    vx
    vy
    vw
    vn
    df-inftm
    @17
    @18
    cB
    cB
    cB
    @34
    cvv
    inftm.b
    cW
    cbs
    fvex
    eqeltri
    #
    @37
    xpex
    @15
    vx
    vy
    cB
    cB
    opabssxp
    #
    ssexi
    fvmpt
    syl
    @38
    syl6eqss
end
