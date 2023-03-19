include "wcel.mm"
include "wss.mm"
include "cfv.mm"
include "wceq.mm"
include "cv.mm"
include "cvsca.mm"
include "co.mm"
include "csn.mm"
include "cdif.mm"
include "wn.mm"
include "csca.mm"
include "cbs.mm"
include "c0g.mm"
include "wral.mm"
include "w3a.mm"
include "clbs.mm"
include "cdm.mm"
include "wb.mm"
include "elfvdm.mm"
include "eleq2s.mm"
include "eqid.mm"
include "islbs.mm"
include "syl.mm"
include "ibi.mm"
include "simp2d.mm"

theorem lbssp
  let cB: class B
  let cJ: class J
  let cN: class N
  let cV: class V
  let cW: class W
  let cA: class A
  let vy: setvar y
  let vx: setvar x
  let cE: class E
  let cF: class F
  let cK: class K
  let c.x: class .x.
  let c.0: class .0.
  assume lbsss.v: |- V = ( Base ` W )
  assume lbsss.j: |- J = ( LBasis ` W )
  assume lbssp.n: |- N = ( LSpan ` W )


  assert |- ( B e. J -> ( N ` B ) = V )

  proof
    cB
    cJ
    wcel
    #
    cB
    cV
    wss
    #
    cB
    cN
    cfv
    cV
    wceq
    #
    vy
    cv
    vx
    cv
    #
    cW
    cvsca
    cfv
    #
    co
    cB
    @3
    csn
    cdif
    cN
    cfv
    wcel
    wn
    vy
    cW
    csca
    cfv
    #
    cbs
    cfv
    #
    @5
    c0g
    cfv
    #
    csn
    cdif
    wral
    vx
    cB
    wral
    #
    @0
    @1
    @2
    @8
    w3a
    #
    @0
    cW
    clbs
    cdm
    #
    wcel
    #
    @0
    @9
    wb
    @11
    cB
    cW
    clbs
    cfv
    cJ
    cB
    cW
    clbs
    elfvdm
    lbsss.j
    eleq2s
    vx
    vy
    cB
    @4
    @5
    cJ
    @6
    cN
    cV
    cW
    @10
    @7
    lbsss.v
    @5
    eqid
    @4
    eqid
    @6
    eqid
    lbsss.j
    lbssp.n
    @7
    eqid
    islbs
    syl
    ibi
    simp2d
end
