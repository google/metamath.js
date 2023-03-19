include "wcel.mm"
include "csn.mm"
include "cixp.mm"
include "cv.mm"
include "wfn.mm"
include "cfv.mm"
include "wral.mm"
include "wa.mm"
include "cab.mm"
include "csb.mm"
include "dfixp.mm"
include "wsbc.mm"
include "ralsnsg.mm"
include "sbcel12.mm"
include "csbfv2g.mm"
include "csbvarg.mm"
include "fveq2d.mm"
include "eqtrd.mm"
include "eleq1d.mm"
include "syl5bb.mm"
include "bitrd.mm"
include "anbi2d.mm"
include "abbidv.mm"
include "syl5eq.mm"

theorem ixpsnval
  let vx: setvar x
  let cB: class B
  let vf: setvar f
  let cV: class V
  let cX: class X

  disjoint B f
  disjoint V f
  disjoint X f
  disjoint X x
  disjoint f x
  assert |- ( X e. V -> X_ x e. { X } B = { f | ( f Fn { X } /\ ( f ` X ) e. [_ X / x ]_ B ) } )

  proof
    cX
    cV
    wcel
    #
    vx
    cX
    csn
    #
    cB
    cixp
    vf
    cv
    #
    @1
    wfn
    #
    vx
    cv
    #
    @2
    cfv
    #
    cB
    wcel
    #
    vx
    @1
    wral
    #
    wa
    #
    vf
    cab
    @3
    cX
    @2
    cfv
    #
    vx
    cX
    cB
    csb
    #
    wcel
    #
    wa
    #
    vf
    cab
    vx
    @1
    cB
    vf
    dfixp
    @0
    @8
    @12
    vf
    @0
    @7
    @11
    @3
    @0
    @7
    @6
    vx
    cX
    wsbc
    #
    @11
    @6
    vx
    cX
    cV
    ralsnsg
    @13
    vx
    cX
    @5
    csb
    #
    @10
    wcel
    @0
    @11
    vx
    cX
    @5
    cB
    sbcel12
    @0
    @14
    @9
    @10
    @0
    @14
    vx
    cX
    @4
    csb
    #
    @2
    cfv
    @9
    vx
    cX
    @4
    cV
    @2
    csbfv2g
    @0
    @15
    cX
    @2
    vx
    cX
    cV
    csbvarg
    fveq2d
    eqtrd
    eleq1d
    syl5bb
    bitrd
    anbi2d
    abbidv
    syl5eq
end
