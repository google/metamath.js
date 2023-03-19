include "cupgr.mm"
include "wcel.mm"
include "cspths.mm"
include "cfv.mm"
include "cv.mm"
include "ctrls.mm"
include "wbr.mm"
include "ccnv.mm"
include "wfun.mm"
include "wa.mm"
include "copab.mm"
include "cwlks.mm"
include "spthsfval.mm"
include "wb.mm"
include "wi.mm"
include "upgrwlkdvde.mm"
include "3exp.mm"
include "com23.mm"
include "imp.mm"
include "pm4.71d.mm"
include "istrl.mm"
include "syl6rbbr.mm"
include "ex.mm"
include "pm5.32rd.mm"
include "opabbidv.mm"
include "syl5eq.mm"

theorem upgrspthswlk
  let vf: setvar f
  let cG: class G
  let vp: setvar p
  let cF: class F
  let vk: setvar k
  let cP: class P

  disjoint G f
  disjoint G p
  disjoint f p
  disjoint F k
  disjoint G k
  disjoint P k
  assert |- ( G e. UPGraph -> ( SPaths ` G ) = { <. f , p >. | ( f ( Walks ` G ) p /\ Fun `' p ) } )

  proof
    cG
    cupgr
    wcel
    #
    cG
    cspths
    cfv
    vf
    cv
    #
    vp
    cv
    #
    cG
    ctrls
    cfv
    wbr
    #
    @2
    ccnv
    wfun
    #
    wa
    #
    vf
    vp
    copab
    @1
    @2
    cG
    cwlks
    cfv
    wbr
    #
    @4
    wa
    #
    vf
    vp
    copab
    vf
    cG
    vp
    spthsfval
    @0
    @5
    @7
    vf
    vp
    @0
    @4
    @3
    @6
    @0
    @4
    @3
    @6
    wb
    @0
    @4
    wa
    #
    @6
    @6
    @1
    ccnv
    wfun
    #
    wa
    @3
    @8
    @6
    @9
    @0
    @4
    @6
    @9
    wi
    @0
    @6
    @4
    @9
    @0
    @6
    @4
    @9
    @2
    @1
    cG
    upgrwlkdvde
    3exp
    com23
    imp
    pm4.71d
    @2
    @1
    cG
    istrl
    syl6rbbr
    ex
    pm5.32rd
    opabbidv
    syl5eq
end
