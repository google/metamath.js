include "cclwwlk.mm"
include "cfv.mm"
include "cv.mm"
include "c0.mm"
include "wne.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cpr.mm"
include "cedg.mm"
include "wcel.mm"
include "cc0.mm"
include "chash.mm"
include "cmin.mm"
include "cfzo.mm"
include "wral.mm"
include "clsw.mm"
include "w3a.mm"
include "cvtx.mm"
include "cword.mm"
include "crab.mm"
include "eqid.mm"
include "clwwlk.mm"
include "ssrab2.mm"
include "eqsstri.mm"

theorem clwwlksswrd
  let cG: class G
  let vi: setvar i
  let vw: setvar w


  assert |- ( ClWWalks ` G ) C_ Word ( Vtx ` G )

  proof
    cG
    cclwwlk
    cfv
    vw
    cv
    #
    c0
    wne
    vi
    cv
    #
    @0
    cfv
    @1
    c1
    caddc
    co
    @0
    cfv
    cpr
    cG
    cedg
    cfv
    #
    wcel
    vi
    cc0
    @0
    chash
    cfv
    c1
    cmin
    co
    cfzo
    co
    wral
    @0
    clsw
    cfv
    cc0
    @0
    cfv
    cpr
    @2
    wcel
    w3a
    #
    vw
    cG
    cvtx
    cfv
    #
    cword
    #
    crab
    @5
    vw
    vi
    @2
    cG
    @4
    @4
    eqid
    @2
    eqid
    clwwlk
    @3
    vw
    @5
    ssrab2
    eqsstri
end
