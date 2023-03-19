include "c2.mm"
include "cmul.mm"
include "wbr.mm"
include "wn.mm"
include "wo.mm"
include "wi.mm"
include "ax-1.mm"
include "mpd.mm"
include "df-or.mm"
include "mpbir.mm"

theorem 2bornot2b
  let cB: class B


  assert |- ( 2 x. B \/ -. 2 x. B )

  proof
    c2
    cB
    cmul
    wbr
    #
    @0
    wn
    #
    wo
    @1
    @1
    wi
    @1
    @0
    @1
    wi
    #
    @1
    @1
    @0
    ax-1
    @1
    @2
    ax-1
    mpd
    @0
    @1
    df-or
    mpbir
end
