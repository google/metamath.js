include "cxp.mm"
include "cvv.mm"
include "cpw.mm"
include "wf.mm"
include "cv.mm"
include "csn.mm"
include "chom.mm"
include "cfv.mm"
include "cmpt.mm"
include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "snssi.mm"
include "adantl.mm"
include "ssv.mm"
include "xpss12.mm"
include "sylancl.mm"
include "snex.mm"
include "fvex.mm"
include "xpex.mm"
include "elpw.mm"
include "sylibr.mm"
include "eqid.mm"
include "fmptd.mm"
include "homafval.mm"
include "feq1d.mm"
include "mpbird.mm"

theorem homaf
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cH: class H
  let vc: setvar c
  let vx: setvar x
  let vz: setvar z
  let cJ: class J
  let cX: class X
  let cY: class Y
  assume homarcl.h: |- H = ( HomA ` C )
  assume homafval.b: |- B = ( Base ` C )
  assume homafval.c: |- ( ph -> C e. Cat )


  assert |- ( ph -> H : ( B X. B ) --> ~P ( ( B X. B ) X. _V ) )

  proof
    wph
    cB
    cB
    cxp
    #
    @0
    cvv
    cxp
    #
    cpw
    #
    cH
    wf
    @0
    @2
    vx
    @0
    vx
    cv
    #
    csn
    #
    @3
    cC
    chom
    cfv
    #
    cfv
    #
    cxp
    #
    cmpt
    #
    wf
    wph
    vx
    @0
    @7
    @2
    @8
    wph
    @3
    @0
    wcel
    #
    wa
    #
    @7
    @1
    wss
    #
    @7
    @2
    wcel
    @10
    @4
    @0
    wss
    #
    @6
    cvv
    wss
    @11
    @9
    @12
    wph
    @3
    @0
    snssi
    adantl
    @6
    ssv
    @4
    @0
    @6
    cvv
    xpss12
    sylancl
    @7
    @1
    @4
    @6
    @3
    snex
    @3
    @5
    fvex
    xpex
    elpw
    sylibr
    @8
    eqid
    fmptd
    wph
    @0
    @2
    cH
    @8
    wph
    vx
    cB
    cC
    cH
    @5
    homarcl.h
    homafval.b
    homafval.c
    @5
    eqid
    homafval
    feq1d
    mpbird
end
