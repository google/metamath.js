include "cwlks.mm"
include "cfv.mm"
include "wbr.mm"
include "ccnv.mm"
include "wfun.mm"
include "ctrls.mm"
include "1wlkd.mm"
include "cs1.mm"
include "funcnvs1.mm"
include "cnveqi.mm"
include "funeqi.mm"
include "mpbir.mm"
include "istrl.mm"
include "sylanblrc.mm"

theorem 1trld
  let wph: wff ph
  let cP: class P
  let cF: class F
  let cG: class G
  let cI: class I
  let cJ: class J
  let cV: class V
  let cX: class X
  let cY: class Y
  let vk: setvar k
  assume 1wlkd.p: |- P = <" X Y ">
  assume 1wlkd.f: |- F = <" J ">
  assume 1wlkd.x: |- ( ph -> X e. V )
  assume 1wlkd.y: |- ( ph -> Y e. V )
  assume 1wlkd.l: |- ( ( ph /\ X = Y ) -> ( I ` J ) = { X } )
  assume 1wlkd.j: |- ( ( ph /\ X =/= Y ) -> { X , Y } C_ ( I ` J ) )
  assume 1wlkd.v: |- V = ( Vtx ` G )
  assume 1wlkd.i: |- I = ( iEdg ` G )


  assert |- ( ph -> F ( Trails ` G ) P )

  proof
    wph
    cF
    cP
    cG
    cwlks
    cfv
    wbr
    cF
    ccnv
    #
    wfun
    #
    cF
    cP
    cG
    ctrls
    cfv
    wbr
    wph
    cP
    cF
    cG
    cI
    cJ
    cV
    cX
    cY
    1wlkd.p
    1wlkd.f
    1wlkd.x
    1wlkd.y
    1wlkd.l
    1wlkd.j
    1wlkd.v
    1wlkd.i
    1wlkd
    @1
    cJ
    cs1
    #
    ccnv
    #
    wfun
    cJ
    funcnvs1
    @0
    @3
    cF
    @2
    1wlkd.f
    cnveqi
    funeqi
    mpbir
    cP
    cF
    cG
    istrl
    sylanblrc
end
