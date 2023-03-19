include "wcel.mm"
include "wa.mm"
include "ctx.mm"
include "co.mm"
include "cv.mm"
include "cxp.mm"
include "cmpt2.mm"
include "crn.mm"
include "ctg.mm"
include "cfv.mm"
include "wss.mm"
include "wrex.mm"
include "wral.mm"
include "eqid.mm"
include "txval.mm"
include "eleq2d.mm"
include "cvv.mm"
include "wb.mm"
include "txbasex.mm"
include "eltg2b.mm"
include "syl.mm"
include "vex.mm"
include "xpex.mm"
include "rgen2w.mm"
include "wceq.mm"
include "eleq2.mm"
include "sseq1.mm"
include "anbi12d.mm"
include "rexrnmpt2.mm"
include "ax-mp.mm"
include "ralbii.mm"
include "syl6bb.mm"
include "bitrd.mm"

theorem eltx
  let vx: setvar x
  let vy: setvar y
  let cS: class S
  let cJ: class J
  let cK: class K
  let cV: class V
  let cW: class W
  let vp: setvar p
  let vz: setvar z

  disjoint p x
  disjoint p y
  disjoint J p
  disjoint x y
  disjoint J x
  disjoint J y
  disjoint K p
  disjoint K x
  disjoint K y
  disjoint S p
  disjoint S x
  disjoint S y
  disjoint p z
  disjoint x z
  disjoint y z
  disjoint J z
  disjoint K z
  disjoint S z
  assert |- ( ( J e. V /\ K e. W ) -> ( S e. ( J tX K ) <-> A. p e. S E. x e. J E. y e. K ( p e. ( x X. y ) /\ ( x X. y ) C_ S ) ) )

  proof
    cJ
    cV
    wcel
    cK
    cW
    wcel
    wa
    #
    cS
    cJ
    cK
    ctx
    co
    #
    wcel
    cS
    vx
    vy
    cJ
    cK
    vx
    cv
    #
    vy
    cv
    #
    cxp
    #
    cmpt2
    #
    crn
    #
    ctg
    cfv
    #
    wcel
    #
    vp
    cv
    #
    @4
    wcel
    #
    @4
    cS
    wss
    #
    wa
    #
    vy
    cK
    wrex
    vx
    cJ
    wrex
    #
    vp
    cS
    wral
    #
    @0
    @1
    @7
    cS
    vx
    vy
    @6
    cJ
    cK
    cV
    cW
    @6
    eqid
    #
    txval
    eleq2d
    @0
    @8
    @9
    vz
    cv
    #
    wcel
    #
    @16
    cS
    wss
    #
    wa
    #
    vz
    @6
    wrex
    #
    vp
    cS
    wral
    #
    @14
    @0
    @6
    cvv
    wcel
    @8
    @21
    wb
    vx
    vy
    @6
    cJ
    cK
    cV
    cW
    @15
    txbasex
    vp
    vz
    cS
    @6
    cvv
    eltg2b
    syl
    @20
    @13
    vp
    cS
    @4
    cvv
    wcel
    #
    vy
    cK
    wral
    vx
    cJ
    wral
    @20
    @13
    wb
    @22
    vx
    vy
    cJ
    cK
    @2
    @3
    vx
    vex
    vy
    vex
    xpex
    rgen2w
    @19
    @12
    vx
    vy
    vz
    cJ
    cK
    @4
    @5
    cvv
    @5
    eqid
    @16
    @4
    wceq
    @17
    @10
    @18
    @11
    @16
    @4
    @9
    eleq2
    @16
    @4
    cS
    sseq1
    anbi12d
    rexrnmpt2
    ax-mp
    ralbii
    syl6bb
    bitrd
end
