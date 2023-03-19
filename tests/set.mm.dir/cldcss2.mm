include "chl.mm"
include "wcel.mm"
include "ccld.mm"
include "cfv.mm"
include "cin.mm"
include "cv.mm"
include "wa.mm"
include "cldcss.mm"
include "elin.mm"
include "syl6bbr.mm"
include "eqrdv.mm"

theorem cldcss2
  let cC: class C
  let cJ: class J
  let cL: class L
  let cV: class V
  let cW: class W
  let vx: setvar x
  assume cldcss.v: |- V = ( Base ` W )
  assume cldcss.j: |- J = ( TopOpen ` W )
  assume cldcss.l: |- L = ( LSubSp ` W )
  assume cldcss.c: |- C = ( CSubSp ` W )


  assert |- ( W e. CHil -> C = ( L i^i ( Clsd ` J ) ) )

  proof
    cW
    chl
    wcel
    #
    vx
    cC
    cL
    cJ
    ccld
    cfv
    #
    cin
    #
    @0
    vx
    cv
    #
    cC
    wcel
    @3
    cL
    wcel
    @3
    @1
    wcel
    wa
    @3
    @2
    wcel
    cC
    @3
    cJ
    cL
    cV
    cW
    cldcss.v
    cldcss.j
    cldcss.l
    cldcss.c
    cldcss
    @3
    cL
    @1
    elin
    syl6bbr
    eqrdv
end
