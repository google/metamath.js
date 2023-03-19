include "wcel.mm"
include "cn0.mm"
include "cc0.mm"
include "cv.mm"
include "cfzo.mm"
include "co.mm"
include "cmap.mm"
include "ciun.mm"
include "wf.mm"
include "wrex.mm"
include "cab.mm"
include "cword.mm"
include "eliun.mm"
include "cvv.mm"
include "wb.mm"
include "ovex.mm"
include "elmapg.mm"
include "mpan2.mm"
include "rexbidv.mm"
include "syl5bb.mm"
include "abbi2dv.mm"
include "df-word.mm"
include "syl6reqr.mm"

theorem wrdval
  let cS: class S
  let cV: class V
  let vl: setvar l
  let vw: setvar w
  let cW: class W

  disjoint S l
  disjoint V l
  disjoint l w
  disjoint S w
  disjoint V w
  disjoint W l
  disjoint W w
  assert |- ( S e. V -> Word S = U_ l e. NN0 ( S ^m ( 0 ..^ l ) ) )

  proof
    cS
    cV
    wcel
    #
    vl
    cn0
    cS
    cc0
    vl
    cv
    #
    cfzo
    co
    #
    cmap
    co
    #
    ciun
    #
    @2
    cS
    vw
    cv
    #
    wf
    #
    vl
    cn0
    wrex
    #
    vw
    cab
    cS
    cword
    @0
    @7
    vw
    @4
    @5
    @4
    wcel
    @5
    @3
    wcel
    #
    vl
    cn0
    wrex
    @0
    @7
    vl
    @5
    cn0
    @3
    eliun
    @0
    @8
    @6
    vl
    cn0
    @0
    @2
    cvv
    wcel
    @8
    @6
    wb
    cc0
    @1
    cfzo
    ovex
    cS
    @2
    @5
    cV
    cvv
    elmapg
    mpan2
    rexbidv
    syl5bb
    abbi2dv
    vw
    cS
    vl
    df-word
    syl6reqr
end
