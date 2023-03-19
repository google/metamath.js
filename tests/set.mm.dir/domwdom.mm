include "cdom.mm"
include "wbr.mm"
include "cwdom.mm"
include "c0.mm"
include "wceq.mm"
include "cv.mm"
include "wfo.mm"
include "wex.mm"
include "wo.mm"
include "wn.mm"
include "wa.mm"
include "csdm.mm"
include "wne.mm"
include "df-ne.mm"
include "biimpri.mm"
include "adantl.mm"
include "wb.mm"
include "cvv.mm"
include "wcel.mm"
include "reldom.mm"
include "brrelexi.mm"
include "0sdomg.mm"
include "syl.mm"
include "adantr.mm"
include "mpbird.mm"
include "simpl.mm"
include "fodomr.mm"
include "syl2anc.mm"
include "ex.mm"
include "orrd.mm"
include "brrelex2i.mm"
include "brwdom.mm"

theorem domwdom
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cF: class F
  let cZ: class Z


  assert |- ( X ~<_ Y -> X ~<_* Y )

  proof
    cX
    cY
    cdom
    wbr
    #
    cX
    cY
    cwdom
    wbr
    #
    cX
    c0
    wceq
    #
    cY
    cX
    vy
    cv
    wfo
    vy
    wex
    #
    wo
    #
    @0
    @2
    @3
    @0
    @2
    wn
    #
    @3
    @0
    @5
    wa
    #
    c0
    cX
    csdm
    wbr
    #
    @0
    @3
    @6
    @7
    cX
    c0
    wne
    #
    @5
    @8
    @0
    @8
    @5
    cX
    c0
    df-ne
    biimpri
    adantl
    @0
    @7
    @8
    wb
    #
    @5
    @0
    cX
    cvv
    wcel
    @9
    cX
    cY
    cdom
    reldom
    brrelexi
    cX
    cvv
    0sdomg
    syl
    adantr
    mpbird
    @0
    @5
    simpl
    cY
    cX
    vy
    fodomr
    syl2anc
    ex
    orrd
    @0
    cY
    cvv
    wcel
    @1
    @4
    wb
    cX
    cY
    cdom
    reldom
    brrelex2i
    vy
    cvv
    cX
    cY
    brwdom
    syl
    mpbird
end
