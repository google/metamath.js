include "wcel.mm"
include "cc0.mm"
include "wceq.mm"
include "cv.mm"
include "co.mm"
include "wral.mm"
include "cn.mm"
include "crab.mm"
include "c0.mm"
include "wa.mm"
include "oveq1.mm"
include "mulg0.mm"
include "sylan9eqr.mm"
include "adantrr.mm"
include "eqeq1d.mm"
include "ralbidv.mm"
include "elrab.mm"
include "simprbi.mm"
include "oveq2.mm"
include "rspcva.mm"
include "sylan2.mm"
include "cvv.mm"
include "wo.mm"
include "cbs.mm"
include "cfv.mm"
include "elfvex.mm"
include "eleq2s.mm"
include "eqid.mm"
include "gexlem1.mm"
include "syl.mm"
include "mpjaodan.mm"

theorem gexid
  let cA: class A
  let c.x: class .x.
  let cE: class E
  let cG: class G
  let cX: class X
  let c.0: class .0.
  let vx: setvar x
  let vy: setvar y
  let cN: class N
  let cV: class V
  assume gexcl.1: |- X = ( Base ` G )
  assume gexcl.2: |- E = ( gEx ` G )
  assume gexid.3: |- .x. = ( .g ` G )
  assume gexid.4: |- .0. = ( 0g ` G )


  assert |- ( A e. X -> ( E .x. A ) = .0. )

  proof
    cA
    cX
    wcel
    #
    cE
    cc0
    wceq
    #
    vy
    cv
    #
    vx
    cv
    #
    c.x
    co
    #
    c.0
    wceq
    #
    vx
    cX
    wral
    #
    vy
    cn
    crab
    #
    c0
    wceq
    #
    wa
    #
    cE
    cA
    c.x
    co
    #
    c.0
    wceq
    #
    cE
    @7
    wcel
    #
    @0
    @1
    @11
    @8
    @1
    @0
    @10
    cc0
    cA
    c.x
    co
    c.0
    cE
    cc0
    cA
    c.x
    oveq1
    cX
    c.x
    cG
    cA
    c.0
    gexcl.1
    gexid.4
    gexid.3
    mulg0
    sylan9eqr
    adantrr
    @12
    @0
    cE
    @3
    c.x
    co
    #
    c.0
    wceq
    #
    vx
    cX
    wral
    #
    @11
    @12
    cE
    cn
    wcel
    @15
    @6
    @15
    vy
    cE
    cn
    @2
    cE
    wceq
    #
    @5
    @14
    vx
    cX
    @16
    @4
    @13
    c.0
    @2
    cE
    @3
    c.x
    oveq1
    eqeq1d
    ralbidv
    elrab
    simprbi
    @14
    @11
    vx
    cA
    cX
    @3
    cA
    wceq
    @13
    @10
    c.0
    @3
    cA
    cE
    c.x
    oveq2
    eqeq1d
    rspcva
    sylan2
    @0
    cG
    cvv
    wcel
    #
    @9
    @12
    wo
    @17
    cA
    cG
    cbs
    cfv
    cX
    cA
    cG
    cbs
    elfvex
    gexcl.1
    eleq2s
    vx
    vy
    c.x
    cE
    cG
    @7
    cvv
    cX
    c.0
    gexcl.1
    gexid.3
    gexid.4
    gexcl.2
    @7
    eqid
    gexlem1
    syl
    mpjaodan
end
