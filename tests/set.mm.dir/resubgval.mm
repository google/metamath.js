include "cr.mm"
include "ccnfld.mm"
include "csubg.mm"
include "cfv.mm"
include "wcel.mm"
include "cmin.mm"
include "co.mm"
include "wceq.mm"
include "csubrg.mm"
include "crefld.mm"
include "cdr.mm"
include "resubdrg.mm"
include "simpli.mm"
include "subrgsubg.mm"
include "ax-mp.mm"
include "cnfldsub.mm"
include "df-refld.mm"
include "subgsub.mm"
include "mp3an1.mm"

theorem resubgval
  let c.mi: class .-
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  assume resubgval.m: |- .- = ( -g ` RRfld )


  assert |- ( ( X e. RR /\ Y e. RR ) -> ( X - Y ) = ( X .- Y ) )

  proof
    cr
    ccnfld
    csubg
    cfv
    wcel
    #
    cX
    cr
    wcel
    cY
    cr
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
    cr
    ccnfld
    csubrg
    cfv
    wcel
    #
    @0
    @1
    crefld
    cdr
    wcel
    resubdrg
    simpli
    cr
    ccnfld
    subrgsubg
    ax-mp
    cr
    ccnfld
    crefld
    cmin
    c.mi
    cX
    cY
    cnfldsub
    df-refld
    resubgval.m
    subgsub
    mp3an1
end
