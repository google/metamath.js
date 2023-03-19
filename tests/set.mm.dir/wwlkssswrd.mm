include "cwwlks.mm"
include "cfv.mm"
include "cword.mm"
include "cv.mm"
include "wcel.mm"
include "cvv.mm"
include "wwlkbp.mm"
include "simprd.mm"
include "ssriv.mm"

theorem wwlkssswrd
  let cG: class G
  let cV: class V
  let vw: setvar w
  assume wwlkssswrd.v: |- V = ( Vtx ` G )


  assert |- ( WWalks ` G ) C_ Word V

  proof
    vw
    cG
    cwwlks
    cfv
    #
    cV
    cword
    #
    vw
    cv
    #
    @0
    wcel
    cG
    cvv
    wcel
    @2
    @1
    wcel
    cG
    cV
    @2
    wwlkssswrd.v
    wwlkbp
    simprd
    ssriv
end
