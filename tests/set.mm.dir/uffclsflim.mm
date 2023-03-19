include "cufil.mm"
include "cfv.mm"
include "wcel.mm"
include "cfcls.mm"
include "co.mm"
include "cflim.mm"
include "cv.mm"
include "wa.mm"
include "wss.mm"
include "cfil.mm"
include "wrex.mm"
include "wb.mm"
include "ufilfil.mm"
include "fclsfnflim.mm"
include "syl.mm"
include "biimpa.mm"
include "simprrr.mm"
include "wceq.mm"
include "simpll.mm"
include "simprl.mm"
include "simprrl.mm"
include "ufilmax.mm"
include "syl3anc.mm"
include "oveq2d.mm"
include "eleqtrrd.mm"
include "rexlimddv.mm"
include "ex.mm"
include "ssrdv.mm"
include "flimfcls.mm"
include "a1i.mm"
include "eqssd.mm"

theorem uffclsflim
  let cF: class F
  let cJ: class J
  let cX: class X
  let vn: setvar n
  let vo: setvar o
  let vx: setvar x
  let cA: class A
  let vf: setvar f
  let vg: setvar g
  let vj: setvar j
  let vs: setvar s
  let vy: setvar y
  let cL: class L
  let cN: class N
  let cY: class Y
  let cS: class S


  assert |- ( F e. ( UFil ` X ) -> ( J fClus F ) = ( J fLim F ) )

  proof
    cF
    cX
    cufil
    cfv
    wcel
    #
    cJ
    cF
    cfcls
    co
    #
    cJ
    cF
    cflim
    co
    #
    @0
    vx
    @1
    @2
    @0
    vx
    cv
    #
    @1
    wcel
    #
    @3
    @2
    wcel
    #
    @0
    @4
    wa
    #
    cF
    vf
    cv
    #
    wss
    #
    @3
    cJ
    @7
    cflim
    co
    #
    wcel
    #
    wa
    #
    @5
    vf
    cX
    cfil
    cfv
    #
    @0
    @4
    @11
    vf
    @12
    wrex
    #
    @0
    cF
    @12
    wcel
    @4
    @13
    wb
    cF
    cX
    ufilfil
    @3
    vf
    cF
    cJ
    cX
    fclsfnflim
    syl
    biimpa
    @6
    @7
    @12
    wcel
    #
    @11
    wa
    #
    wa
    #
    @3
    @9
    @2
    @6
    @14
    @8
    @10
    simprrr
    @16
    cF
    @7
    cJ
    cflim
    @16
    @0
    @14
    @8
    cF
    @7
    wceq
    @0
    @4
    @15
    simpll
    @6
    @14
    @11
    simprl
    @6
    @14
    @8
    @10
    simprrl
    cF
    @7
    cX
    ufilmax
    syl3anc
    oveq2d
    eleqtrrd
    rexlimddv
    ex
    ssrdv
    @2
    @1
    wss
    @0
    cF
    cJ
    flimfcls
    a1i
    eqssd
end
