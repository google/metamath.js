include "cc0.mm"
include "cs2.mm"
include "csn.mm"
include "cword.mm"
include "cdm.mm"
include "wcel.mm"
include "c0ex.mm"
include "snid.mm"
include "id.mm"
include "s2cld.mm"
include "ax-mp.mm"
include "cpr.mm"
include "cs1.mm"
include "dmeqi.mm"
include "s1dm.mm"
include "eqtri.mm"
include "wrdeqi.mm"
include "3eltr4i.mm"

theorem wlk2v2elem1
  let cF: class F
  let cI: class I
  let cX: class X
  let cY: class Y
  assume wlk2v2e.i: |- I = <" { X , Y } ">
  assume wlk2v2e.f: |- F = <" 0 0 ">


  assert |- F e. Word dom I

  proof
    cc0
    cc0
    cs2
    #
    cc0
    csn
    #
    cword
    #
    cF
    cI
    cdm
    #
    cword
    cc0
    @1
    wcel
    #
    @0
    @2
    wcel
    cc0
    c0ex
    snid
    @4
    cc0
    cc0
    @1
    @4
    id
    #
    @5
    s2cld
    ax-mp
    wlk2v2e.f
    @3
    @1
    @3
    cX
    cY
    cpr
    #
    cs1
    #
    cdm
    @1
    cI
    @7
    wlk2v2e.i
    dmeqi
    @6
    s1dm
    eqtri
    wrdeqi
    3eltr4i
end
