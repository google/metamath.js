include "wcel.mm"
include "wss.mm"
include "clspn.mm"
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
include "simp1d.mm"

theorem lbsss
  let cB: class B
  let cJ: class J
  let cV: class V
  let cW: class W
  let cA: class A
  let vy: setvar y
  let vx: setvar x
  let cE: class E
  let cF: class F
  let cK: class K
  let cN: class N
  let c.x: class .x.
  let c.0: class .0.
  assume lbsss.v: |- V = ( Base ` W )
  assume lbsss.j: |- J = ( LBasis ` W )


  assert |- ( B e. J -> B C_ V )

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
    cW
    clspn
    cfv
    #
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
    @4
    csn
    cdif
    @2
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
    @6
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
    @3
    @9
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
    @10
    wb
    @12
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
    @5
    @6
    cJ
    @7
    @2
    cV
    cW
    @11
    @8
    lbsss.v
    @6
    eqid
    @5
    eqid
    @7
    eqid
    lbsss.j
    @2
    eqid
    @8
    eqid
    islbs
    syl
    ibi
    simp1d
end
