include "crg.mm"
include "wcel.mm"
include "cabv.mm"
include "cfv.mm"
include "cdm.mm"
include "cv.mm"
include "cc0.mm"
include "wceq.mm"
include "c0g.mm"
include "wb.mm"
include "cmulr.mm"
include "co.mm"
include "cmul.mm"
include "cplusg.mm"
include "caddc.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cbs.mm"
include "wral.mm"
include "cpnf.mm"
include "cico.mm"
include "cmap.mm"
include "crab.mm"
include "df-abv.mm"
include "dmmptss.mm"
include "elfvdm.mm"
include "sseldi.mm"
include "eleq2s.mm"

theorem abvrcl
  let cA: class A
  let cR: class R
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  let c.pl: class .+
  let c.0: class .0.
  let cB: class B
  let cY: class Y
  let vf: setvar f
  let vr: setvar r
  let c.x: class .x.
  let cX: class X
  assume abvf.a: |- A = ( AbsVal ` R )


  assert |- ( F e. A -> R e. Ring )

  proof
    cR
    crg
    wcel
    cF
    cR
    cabv
    cfv
    #
    cA
    cF
    @0
    wcel
    cabv
    cdm
    crg
    cR
    vr
    crg
    vx
    cv
    #
    vf
    cv
    #
    cfv
    #
    cc0
    wceq
    @1
    vr
    cv
    #
    c0g
    cfv
    wceq
    wb
    @1
    vy
    cv
    #
    @4
    cmulr
    cfv
    co
    @2
    cfv
    @3
    @5
    @2
    cfv
    #
    cmul
    co
    wceq
    @1
    @5
    @4
    cplusg
    cfv
    co
    @2
    cfv
    @3
    @6
    caddc
    co
    cle
    wbr
    wa
    vy
    @4
    cbs
    cfv
    #
    wral
    wa
    vx
    @7
    wral
    vf
    cc0
    cpnf
    cico
    co
    @7
    cmap
    co
    crab
    cabv
    vx
    vy
    vf
    vr
    df-abv
    dmmptss
    cF
    cR
    cabv
    elfvdm
    sseldi
    abvf.a
    eleq2s
end
