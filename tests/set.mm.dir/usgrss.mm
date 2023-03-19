include "cusgr.mm"
include "wcel.mm"
include "cdm.mm"
include "wa.mm"
include "cfv.mm"
include "cv.mm"
include "chash.mm"
include "c2.mm"
include "wceq.mm"
include "cpw.mm"
include "crab.mm"
include "ssrab2.mm"
include "wf1.mm"
include "wf.mm"
include "usgrfs.mm"
include "f1f.mm"
include "syl.mm"
include "ffvelrnda.mm"
include "sseldi.mm"
include "elpwid.mm"

theorem usgrss
  let cE: class E
  let cG: class G
  let cV: class V
  let cX: class X
  let vx: setvar x
  assume usgrf1o.e: |- E = ( iEdg ` G )
  assume usgrss.v: |- V = ( Vtx ` G )


  assert |- ( ( G e. USGraph /\ X e. dom E ) -> ( E ` X ) C_ V )

  proof
    cG
    cusgr
    wcel
    #
    cX
    cE
    cdm
    #
    wcel
    wa
    #
    cX
    cE
    cfv
    #
    cV
    @2
    vx
    cv
    chash
    cfv
    c2
    wceq
    #
    vx
    cV
    cpw
    #
    crab
    #
    @5
    @3
    @4
    vx
    @5
    ssrab2
    @0
    @1
    @6
    cX
    cE
    @0
    @1
    @6
    cE
    wf1
    @1
    @6
    cE
    wf
    vx
    cE
    cG
    cV
    usgrss.v
    usgrf1o.e
    usgrfs
    @1
    @6
    cE
    f1f
    syl
    ffvelrnda
    sseldi
    elpwid
end
