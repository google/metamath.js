include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "cfil.mm"
include "wf.mm"
include "cflf.mm"
include "co.mm"
include "cfm.mm"
include "cflim.mm"
include "wceq.mm"
include "wa.mm"
include "cmap.mm"
include "wb.mm"
include "toponmax.mm"
include "filtop.mm"
include "elmapg.mm"
include "syl2an.mm"
include "biimpar.mm"
include "cv.mm"
include "cmpt.mm"
include "flffval.mm"
include "fveq1d.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "eqid.mm"
include "ovex.mm"
include "fvmpt.mm"
include "sylan9eq.mm"
include "syldan.mm"
include "3impa.mm"

theorem flfval
  let cF: class F
  let cJ: class J
  let cL: class L
  let cX: class X
  let cY: class Y
  let vf: setvar f
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( J e. ( TopOn ` X ) /\ L e. ( Fil ` Y ) /\ F : Y --> X ) -> ( ( J fLimf L ) ` F ) = ( J fLim ( ( X FilMap F ) ` L ) ) )

  proof
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    cL
    cY
    cfil
    cfv
    wcel
    #
    cY
    cX
    cF
    wf
    #
    cF
    cJ
    cL
    cflf
    co
    #
    cfv
    #
    cJ
    cL
    cX
    cF
    cfm
    co
    #
    cfv
    #
    cflim
    co
    #
    wceq
    #
    @0
    @1
    wa
    #
    @2
    cF
    cX
    cY
    cmap
    co
    #
    wcel
    #
    @8
    @9
    @11
    @2
    @0
    cX
    cJ
    wcel
    cY
    cL
    wcel
    @11
    @2
    wb
    @1
    cX
    cJ
    toponmax
    cL
    cY
    filtop
    cX
    cY
    cF
    cJ
    cL
    elmapg
    syl2an
    biimpar
    @9
    @11
    @4
    cF
    vf
    @10
    cJ
    cL
    cX
    vf
    cv
    #
    cfm
    co
    #
    cfv
    #
    cflim
    co
    #
    cmpt
    #
    cfv
    @7
    @9
    cF
    @3
    @16
    vf
    cJ
    cL
    cX
    cY
    flffval
    fveq1d
    vf
    cF
    @15
    @7
    @10
    @16
    @12
    cF
    wceq
    #
    @14
    @6
    cJ
    cflim
    @17
    cL
    @13
    @5
    @12
    cF
    cX
    cfm
    oveq2
    fveq1d
    oveq2d
    @16
    eqid
    cJ
    @6
    cflim
    ovex
    fvmpt
    sylan9eq
    syldan
    3impa
end
