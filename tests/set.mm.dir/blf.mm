include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "cxr.mm"
include "cxp.mm"
include "cpw.mm"
include "cbl.mm"
include "wf.mm"
include "cv.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "crab.mm"
include "cmpt2.mm"
include "wral.mm"
include "wa.mm"
include "wss.mm"
include "ssrab2.mm"
include "cdm.mm"
include "wb.mm"
include "elfvdm.mm"
include "elpw2g.mm"
include "syl.mm"
include "mpbiri.mm"
include "a1d.mm"
include "ralrimivv.mm"
include "eqid.mm"
include "fmpt2.mm"
include "sylib.mm"
include "blfval.mm"
include "feq1d.mm"
include "mpbird.mm"

theorem blf
  let cD: class D
  let cX: class X
  let vr: setvar r
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let vz: setvar z
  let cB: class B
  let cC: class C
  let cR: class R
  let cP: class P
  let cS: class S


  assert |- ( D e. ( *Met ` X ) -> ( ball ` D ) : ( X X. RR* ) --> ~P X )

  proof
    cD
    cX
    cxmt
    cfv
    wcel
    #
    cX
    cxr
    cxp
    #
    cX
    cpw
    #
    cD
    cbl
    cfv
    #
    wf
    @1
    @2
    vx
    vr
    cX
    cxr
    vx
    cv
    #
    vy
    cv
    cD
    co
    vr
    cv
    #
    clt
    wbr
    #
    vy
    cX
    crab
    #
    cmpt2
    #
    wf
    #
    @0
    @7
    @2
    wcel
    #
    vr
    cxr
    wral
    vx
    cX
    wral
    @9
    @0
    @10
    vx
    vr
    cX
    cxr
    @0
    @10
    @4
    cX
    wcel
    @5
    cxr
    wcel
    wa
    @0
    @10
    @7
    cX
    wss
    #
    @6
    vy
    cX
    ssrab2
    @0
    cX
    cxmt
    cdm
    #
    wcel
    @10
    @11
    wb
    cD
    cX
    cxmt
    elfvdm
    @7
    cX
    @12
    elpw2g
    syl
    mpbiri
    a1d
    ralrimivv
    vx
    vr
    cX
    cxr
    @7
    @2
    @8
    @8
    eqid
    fmpt2
    sylib
    @0
    @1
    @2
    @3
    @8
    vx
    vy
    cD
    cX
    vr
    blfval
    feq1d
    mpbird
end
