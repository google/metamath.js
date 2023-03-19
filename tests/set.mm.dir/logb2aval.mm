include "cc.mm"
include "cc0.mm"
include "c1.mm"
include "cpr.mm"
include "cdif.mm"
include "wcel.mm"
include "csn.mm"
include "wa.mm"
include "cop.mm"
include "clogb.mm"
include "cfv.mm"
include "co.mm"
include "clog.mm"
include "cdiv.mm"
include "df-ov.mm"
include "logbval.mm"
include "syl5eqr.mm"

theorem logb2aval
  let cB: class B
  let cX: class X
  let vk: setvar k
  let vx: setvar x


  assert |- ( ( B e. ( CC \ { 0 , 1 } ) /\ X e. ( CC \ { 0 } ) ) -> ( logb ` <. B , X >. ) = ( ( log ` X ) / ( log ` B ) ) )

  proof
    cB
    cc
    cc0
    c1
    cpr
    cdif
    wcel
    cX
    cc
    cc0
    csn
    cdif
    wcel
    wa
    cB
    cX
    cop
    clogb
    cfv
    cB
    cX
    clogb
    co
    cX
    clog
    cfv
    cB
    clog
    cfv
    cdiv
    co
    cB
    cX
    clogb
    df-ov
    cB
    cX
    logbval
    syl5eqr
end
