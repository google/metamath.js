include "cv.mm"
include "com.mm"
include "wcel.mm"
include "c0.mm"
include "csn.mm"
include "cdif.mm"
include "eldifi.mm"
include "eleq2s.mm"

theorem bnj923
  let cD: class D
  let vn: setvar n
  assume bnj923.1: |- D = ( _om \ { (/) } )


  assert |- ( n e. D -> n e. _om )

  proof
    vn
    cv
    #
    com
    wcel
    @0
    com
    c0
    csn
    #
    cdif
    cD
    @0
    com
    @1
    eldifi
    bnj923.1
    eleq2s
end
