include "cwlks.mm"
include "cfv.mm"
include "wcel.mm"
include "cv.mm"
include "wbr.mm"
include "cc0.mm"
include "chash.mm"
include "wceq.mm"
include "wa.mm"
include "copab.mm"
include "cclwlks.mm"
include "elopabran.mm"
include "clwlks.mm"
include "eleq2s.mm"

theorem clwlkwlk
  let cG: class G
  let cW: class W
  let cF: class F
  let vf: setvar f
  let vp: setvar p
  let cP: class P


  assert |- ( W e. ( ClWalks ` G ) -> W e. ( Walks ` G ) )

  proof
    cW
    cG
    cwlks
    cfv
    #
    wcel
    cW
    vf
    cv
    #
    vp
    cv
    #
    @0
    wbr
    cc0
    @2
    cfv
    @1
    chash
    cfv
    @2
    cfv
    wceq
    #
    wa
    vf
    vp
    copab
    cG
    cclwlks
    cfv
    @3
    vf
    vp
    cW
    @0
    elopabran
    vf
    cG
    vp
    clwlks
    eleq2s
end
