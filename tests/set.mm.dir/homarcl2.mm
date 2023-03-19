include "co.mm"
include "wcel.mm"
include "cop.mm"
include "cxp.mm"
include "wa.mm"
include "cdm.mm"
include "cfv.mm"
include "elfvdm.mm"
include "df-ov.mm"
include "eleq2s.mm"
include "cvv.mm"
include "cpw.mm"
include "wf.mm"
include "wceq.mm"
include "homarcl.mm"
include "homaf.mm"
include "fdm.mm"
include "syl.mm"
include "eleqtrd.mm"
include "opelxp.mm"
include "sylib.mm"

theorem homarcl2
  let cB: class B
  let cC: class C
  let cF: class F
  let cH: class H
  let cX: class X
  let cY: class Y
  let vf: setvar f
  assume homahom.h: |- H = ( HomA ` C )
  assume homarcl2.b: |- B = ( Base ` C )


  assert |- ( F e. ( X H Y ) -> ( X e. B /\ Y e. B ) )

  proof
    cF
    cX
    cY
    cH
    co
    #
    wcel
    #
    cX
    cY
    cop
    #
    cB
    cB
    cxp
    #
    wcel
    cX
    cB
    wcel
    cY
    cB
    wcel
    wa
    @1
    @2
    cH
    cdm
    #
    @3
    @2
    @4
    wcel
    cF
    @2
    cH
    cfv
    @0
    cF
    @2
    cH
    elfvdm
    cX
    cY
    cH
    df-ov
    eleq2s
    @1
    @3
    @3
    cvv
    cxp
    cpw
    #
    cH
    wf
    @4
    @3
    wceq
    @1
    cB
    cC
    cH
    homahom.h
    homarcl2.b
    cC
    cF
    cH
    cX
    cY
    homahom.h
    homarcl
    homaf
    @3
    @5
    cH
    fdm
    syl
    eleqtrd
    cX
    cY
    cB
    cB
    opelxp
    sylib
end
