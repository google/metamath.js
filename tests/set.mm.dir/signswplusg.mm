include "cvv.mm"
include "wcel.mm"
include "cplusg.mm"
include "cfv.mm"
include "wceq.mm"
include "c1.mm"
include "cneg.mm"
include "cc0.mm"
include "ctp.mm"
include "cv.mm"
include "cif.mm"
include "cmpt2.mm"
include "tpex.mm"
include "mpt2ex.mm"
include "eqeltri.mm"
include "grpplusg.mm"
include "ax-mp.mm"

theorem signswplusg
  let c.pd: class .+^
  let cW: class W
  let va: setvar a
  let vb: setvar b
  assume signsw.p: |- .+^ = ( a e. { -u 1 , 0 , 1 } , b e. { -u 1 , 0 , 1 } |-> if ( b = 0 , a , b ) )
  assume signsw.w: |- W = { <. ( Base ` ndx ) , { -u 1 , 0 , 1 } >. , <. ( +g ` ndx ) , .+^ >. }

  disjoint a b
  assert |- .+^ = ( +g ` W )

  proof
    c.pd
    cvv
    wcel
    c.pd
    cW
    cplusg
    cfv
    wceq
    c.pd
    va
    vb
    c1
    cneg
    #
    cc0
    c1
    ctp
    #
    @1
    vb
    cv
    #
    cc0
    wceq
    va
    cv
    @2
    cif
    #
    cmpt2
    cvv
    signsw.p
    va
    vb
    @1
    @1
    @3
    @0
    cc0
    c1
    tpex
    #
    @4
    mpt2ex
    eqeltri
    @1
    c.pd
    cW
    cvv
    signsw.w
    grpplusg
    ax-mp
end
