include "cwlks.mm"
include "cfv.mm"
include "wrel.mm"
include "wcel.mm"
include "c1st.mm"
include "c2nd.mm"
include "cop.mm"
include "wceq.mm"
include "relwlk.mm"
include "1st2nd.mm"
include "mpan.mm"

theorem wlkop
  let cG: class G
  let cW: class W


  assert |- ( W e. ( Walks ` G ) -> W = <. ( 1st ` W ) , ( 2nd ` W ) >. )

  proof
    cG
    cwlks
    cfv
    #
    wrel
    cW
    @0
    wcel
    cW
    cW
    c1st
    cfv
    cW
    c2nd
    cfv
    cop
    wceq
    cG
    relwlk
    cW
    @0
    1st2nd
    mpan
end
