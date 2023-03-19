include "wss.mm"
include "cword.mm"
include "cc0.mm"
include "cv.mm"
include "chash.mm"
include "cfv.mm"
include "cfzo.mm"
include "co.mm"
include "wf.mm"
include "wcel.mm"
include "fss.mm"
include "expcom.mm"
include "iswrdb.mm"
include "3imtr4g.mm"
include "ssrdv.mm"

theorem sswrd
  let cS: class S
  let cT: class T
  let vw: setvar w


  assert |- ( S C_ T -> Word S C_ Word T )

  proof
    cS
    cT
    wss
    #
    vw
    cS
    cword
    #
    cT
    cword
    #
    @0
    cc0
    vw
    cv
    #
    chash
    cfv
    cfzo
    co
    #
    cS
    @3
    wf
    #
    @4
    cT
    @3
    wf
    #
    @3
    @1
    wcel
    @3
    @2
    wcel
    @5
    @0
    @6
    @4
    cS
    cT
    @3
    fss
    expcom
    cS
    @3
    iswrdb
    cT
    @3
    iswrdb
    3imtr4g
    ssrdv
end
