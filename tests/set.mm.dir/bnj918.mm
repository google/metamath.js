include "cv.mm"
include "cop.mm"
include "csn.mm"
include "cun.mm"
include "cvv.mm"
include "vex.mm"
include "snex.mm"
include "unex.mm"
include "eqeltri.mm"

theorem bnj918
  let cC: class C
  let vf: setvar f
  let vn: setvar n
  let cG: class G
  assume bnj918.1: |- G = ( f u. { <. n , C >. } )


  assert |- G e. _V

  proof
    cG
    vf
    cv
    #
    vn
    cv
    cC
    cop
    #
    csn
    #
    cun
    cvv
    bnj918.1
    @0
    @2
    vf
    vex
    @1
    snex
    unex
    eqeltri
end
