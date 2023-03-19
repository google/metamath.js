include "co.mm"
include "cop.mm"
include "cfv.mm"
include "csn.mm"
include "cxp.mm"
include "df-ov.mm"
include "cv.mm"
include "cvv.mm"
include "homafval.mm"
include "wceq.mm"
include "wa.mm"
include "simpr.mm"
include "sneqd.mm"
include "fveq2d.mm"
include "syl6eqr.mm"
include "xpeq12d.mm"
include "wcel.mm"
include "opelxpi.mm"
include "syl2anc.mm"
include "snex.mm"
include "ovex.mm"
include "xpex.mm"
include "a1i.mm"
include "fvmptd.mm"
include "syl5eq.mm"

theorem homaval
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cH: class H
  let cJ: class J
  let cX: class X
  let cY: class Y
  let vc: setvar c
  let vx: setvar x
  let vz: setvar z
  assume homarcl.h: |- H = ( HomA ` C )
  assume homafval.b: |- B = ( Base ` C )
  assume homafval.c: |- ( ph -> C e. Cat )
  assume homaval.j: |- J = ( Hom ` C )
  assume homaval.x: |- ( ph -> X e. B )
  assume homaval.y: |- ( ph -> Y e. B )


  assert |- ( ph -> ( X H Y ) = ( { <. X , Y >. } X. ( X J Y ) ) )

  proof
    wph
    cX
    cY
    cH
    co
    cX
    cY
    cop
    #
    cH
    cfv
    @0
    csn
    #
    cX
    cY
    cJ
    co
    #
    cxp
    #
    cX
    cY
    cH
    df-ov
    wph
    vz
    @0
    vz
    cv
    #
    csn
    #
    @4
    cJ
    cfv
    #
    cxp
    @3
    cB
    cB
    cxp
    #
    cH
    cvv
    wph
    vz
    cB
    cC
    cH
    cJ
    homarcl.h
    homafval.b
    homafval.c
    homaval.j
    homafval
    wph
    @4
    @0
    wceq
    #
    wa
    #
    @5
    @1
    @6
    @2
    @9
    @4
    @0
    wph
    @8
    simpr
    #
    sneqd
    @9
    @6
    @0
    cJ
    cfv
    @2
    @9
    @4
    @0
    cJ
    @10
    fveq2d
    cX
    cY
    cJ
    df-ov
    syl6eqr
    xpeq12d
    wph
    cX
    cB
    wcel
    cY
    cB
    wcel
    @0
    @7
    wcel
    homaval.x
    homaval.y
    cX
    cY
    cB
    cB
    opelxpi
    syl2anc
    @3
    cvv
    wcel
    wph
    @1
    @2
    @0
    snex
    cX
    cY
    cJ
    ovex
    xpex
    a1i
    fvmptd
    syl5eq
end
