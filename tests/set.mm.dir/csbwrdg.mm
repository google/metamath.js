include "wcel.mm"
include "cv.mm"
include "cword.mm"
include "csb.mm"
include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "wf.mm"
include "cn0.mm"
include "wrex.mm"
include "cab.mm"
include "df-word.mm"
include "csbeq2i.mm"
include "wsbc.mm"
include "sbcrex.mm"
include "sbcfg.mm"
include "csbconstg.mm"
include "csbvarg.mm"
include "feq123d.mm"
include "bitrd.mm"
include "rexbidv.mm"
include "syl5bb.mm"
include "abbidv.mm"
include "csbab.mm"
include "3eqtr4g.mm"
include "syl5eq.mm"

theorem csbwrdg
  let vx: setvar x
  let cS: class S
  let cV: class V
  let vl: setvar l
  let vw: setvar w

  disjoint S x
  disjoint V x
  disjoint S l
  disjoint S w
  disjoint l w
  disjoint l x
  disjoint w x
  disjoint V l
  disjoint V w
  assert |- ( S e. V -> [_ S / x ]_ Word x = Word S )

  proof
    cS
    cV
    wcel
    #
    vx
    cS
    vx
    cv
    #
    cword
    #
    csb
    vx
    cS
    cc0
    vl
    cv
    cfzo
    co
    #
    @1
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
    #
    csb
    #
    cS
    cword
    #
    vx
    cS
    @2
    @7
    vw
    @1
    vl
    df-word
    csbeq2i
    @0
    @6
    vx
    cS
    wsbc
    #
    vw
    cab
    @3
    cS
    @4
    wf
    #
    vl
    cn0
    wrex
    #
    vw
    cab
    @8
    @9
    @0
    @10
    @12
    vw
    @10
    @5
    vx
    cS
    wsbc
    #
    vl
    cn0
    wrex
    @0
    @12
    @5
    vx
    vl
    cS
    cn0
    sbcrex
    @0
    @13
    @11
    vl
    cn0
    @0
    @13
    vx
    cS
    @3
    csb
    #
    vx
    cS
    @1
    csb
    #
    vx
    cS
    @4
    csb
    #
    wf
    @11
    vx
    @3
    @1
    @4
    cV
    cS
    sbcfg
    @0
    @14
    @3
    @15
    cS
    @16
    @4
    vx
    cS
    @4
    cV
    csbconstg
    vx
    cS
    @3
    cV
    csbconstg
    vx
    cS
    cV
    csbvarg
    feq123d
    bitrd
    rexbidv
    syl5bb
    abbidv
    @6
    vx
    vw
    cS
    csbab
    vw
    cS
    vl
    df-word
    3eqtr4g
    syl5eq
end
