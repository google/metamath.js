include "c1.mm"
include "cneg.mm"
include "cc0.mm"
include "ctp.mm"
include "cvv.mm"
include "wcel.mm"
include "cbs.mm"
include "cfv.mm"
include "wceq.mm"
include "tpex.mm"
include "grpbase.mm"
include "ax-mp.mm"

theorem signswbase
  let c.pd: class .+^
  let cW: class W
  let va: setvar a
  let vb: setvar b
  assume signsw.p: |- .+^ = ( a e. { -u 1 , 0 , 1 } , b e. { -u 1 , 0 , 1 } |-> if ( b = 0 , a , b ) )
  assume signsw.w: |- W = { <. ( Base ` ndx ) , { -u 1 , 0 , 1 } >. , <. ( +g ` ndx ) , .+^ >. }


  assert |- { -u 1 , 0 , 1 } = ( Base ` W )

  proof
    c1
    cneg
    #
    cc0
    c1
    ctp
    #
    cvv
    wcel
    @1
    cW
    cbs
    cfv
    wceq
    @0
    cc0
    c1
    tpex
    @1
    c.pd
    cW
    cvv
    signsw.w
    grpbase
    ax-mp
end
