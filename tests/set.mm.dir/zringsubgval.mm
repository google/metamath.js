include "cz.mm"
include "ccnfld.mm"
include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "cmin.mm"
include "co.mm"
include "wceq.mm"
include "csubrg.mm"
include "zsubrg.mm"
include "subrgsubg.mm"
include "ax-mp.mm"
include "zring.mm"
include "cnfldsub.mm"
include "df-zring.mm"
include "subgsub.mm"
include "mp3an1.mm"

theorem zringsubgval
  let c.mi: class .-
  let cX: class X
  let cY: class Y
  let vk: setvar k
  let vx: setvar x
  assume zringsubgval.m: |- .- = ( -g ` ZZring )


  assert |- ( ( X e. ZZ /\ Y e. ZZ ) -> ( X - Y ) = ( X .- Y ) )

  proof
    cz
    ccnfld
    csubg
    cfv
    wcel
    #
    cX
    cz
    wcel
    cY
    cz
    wcel
    cX
    cY
    cmin
    co
    cX
    cY
    c.mi
    co
    wceq
    cz
    ccnfld
    csubrg
    cfv
    wcel
    @0
    zsubrg
    cz
    ccnfld
    subrgsubg
    ax-mp
    cz
    ccnfld
    zring
    cmin
    c.mi
    cX
    cY
    cnfldsub
    df-zring
    zringsubgval.m
    subgsub
    mp3an1
end
