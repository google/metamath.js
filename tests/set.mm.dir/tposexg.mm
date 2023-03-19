include "wcel.mm"
include "ctpos.mm"
include "cdm.mm"
include "ccnv.mm"
include "c0.mm"
include "csn.mm"
include "cun.mm"
include "crn.mm"
include "cxp.mm"
include "wss.mm"
include "cvv.mm"
include "tposssxp.mm"
include "dmexg.mm"
include "cnvexg.mm"
include "syl.mm"
include "p0ex.mm"
include "unexg.mm"
include "sylancl.mm"
include "rnexg.mm"
include "xpexg.mm"
include "syl2anc.mm"
include "ssexg.mm"
include "sylancr.mm"

theorem tposexg
  let cF: class F
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let vw: setvar w
  let vz: setvar z
  let cG: class G


  assert |- ( F e. V -> tpos F e. _V )

  proof
    cF
    cV
    wcel
    #
    cF
    ctpos
    #
    cF
    cdm
    #
    ccnv
    #
    c0
    csn
    #
    cun
    #
    cF
    crn
    #
    cxp
    #
    wss
    @7
    cvv
    wcel
    #
    @1
    cvv
    wcel
    cF
    tposssxp
    @0
    @5
    cvv
    wcel
    #
    @6
    cvv
    wcel
    @8
    @0
    @3
    cvv
    wcel
    #
    @4
    cvv
    wcel
    @9
    @0
    @2
    cvv
    wcel
    @10
    cF
    cV
    dmexg
    @2
    cvv
    cnvexg
    syl
    p0ex
    @3
    @4
    cvv
    cvv
    unexg
    sylancl
    cF
    cV
    rnexg
    @5
    @6
    cvv
    cvv
    xpexg
    syl2anc
    @1
    @7
    cvv
    ssexg
    sylancr
end
