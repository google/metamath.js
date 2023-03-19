include "clsi.mm"
include "cfv.mm"
include "clsp.mm"
include "clt.mm"
include "wbr.mm"
include "cc0.mm"
include "c1.mm"
include "0lt1.mm"
include "liminf10ex.mm"
include "limsup10ex.mm"
include "breq12i.mm"
include "mpbir.mm"

theorem liminfltlimsupex
  let vn: setvar n
  let cF: class F
  let vk: setvar k
  let vx: setvar x
  assume liminfltlimsupex.1: |- F = ( n e. NN |-> if ( 2 || n , 0 , 1 ) )


  assert |- ( liminf ` F ) < ( limsup ` F )

  proof
    cF
    clsi
    cfv
    #
    cF
    clsp
    cfv
    #
    clt
    wbr
    cc0
    c1
    clt
    wbr
    0lt1
    @0
    cc0
    @1
    c1
    clt
    vn
    cF
    liminfltlimsupex.1
    liminf10ex
    vn
    cF
    liminfltlimsupex.1
    limsup10ex
    breq12i
    mpbir
end
