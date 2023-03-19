include "wcel.mm"
include "wne.mm"
include "wa.mm"
include "csn.mm"
include "cdif.mm"
include "co.mm"
include "cfv.mm"
include "wn.mm"
include "eldifsn.mm"
include "cv.mm"
include "wral.mm"
include "wss.mm"
include "wceq.mm"
include "w3a.mm"
include "clbs.mm"
include "cdm.mm"
include "wb.mm"
include "elfvdm.mm"
include "eleq2s.mm"
include "islbs.mm"
include "syl.mm"
include "ibi.mm"
include "simp3d.mm"
include "oveq2.mm"
include "sneq.mm"
include "difeq2d.mm"
include "fveq2d.mm"
include "eleq12d.mm"
include "notbid.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "rspc2v.mm"
include "syl5com.mm"
include "impl.mm"
include "sylan2br.mm"

theorem lbsind
  let cA: class A
  let cB: class B
  let c.x: class .x.
  let cE: class E
  let cF: class F
  let cJ: class J
  let cK: class K
  let cN: class N
  let cV: class V
  let cW: class W
  let c.0: class .0.
  let vy: setvar y
  let vx: setvar x
  assume lbsss.v: |- V = ( Base ` W )
  assume lbsss.j: |- J = ( LBasis ` W )
  assume lbssp.n: |- N = ( LSpan ` W )
  assume lbsind.f: |- F = ( Scalar ` W )
  assume lbsind.s: |- .x. = ( .s ` W )
  assume lbsind.k: |- K = ( Base ` F )
  assume lbsind.z: |- .0. = ( 0g ` F )


  assert |- ( ( ( B e. J /\ E e. B ) /\ ( A e. K /\ A =/= .0. ) ) -> -. ( A .x. E ) e. ( N ` ( B \ { E } ) ) )

  proof
    cA
    cK
    wcel
    cA
    c.0
    wne
    wa
    cB
    cJ
    wcel
    #
    cE
    cB
    wcel
    #
    wa
    cA
    cK
    c.0
    csn
    cdif
    #
    wcel
    #
    cA
    cE
    c.x
    co
    #
    cB
    cE
    csn
    #
    cdif
    #
    cN
    cfv
    #
    wcel
    #
    wn
    #
    cA
    cK
    c.0
    eldifsn
    @0
    @1
    @3
    @9
    @0
    vy
    cv
    #
    vx
    cv
    #
    c.x
    co
    #
    cB
    @11
    csn
    #
    cdif
    #
    cN
    cfv
    #
    wcel
    #
    wn
    #
    vy
    @2
    wral
    vx
    cB
    wral
    #
    @1
    @3
    wa
    @9
    @0
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
    @18
    @0
    @19
    @20
    @18
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
    @21
    wb
    @23
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
    c.x
    cF
    cJ
    cK
    cN
    cV
    cW
    @22
    c.0
    lbsss.v
    lbsind.f
    lbsind.s
    lbsind.k
    lbsss.j
    lbssp.n
    lbsind.z
    islbs
    syl
    ibi
    simp3d
    @17
    @9
    @10
    cE
    c.x
    co
    #
    @7
    wcel
    #
    wn
    vx
    vy
    cE
    cA
    cB
    @2
    @11
    cE
    wceq
    #
    @16
    @25
    @26
    @12
    @24
    @15
    @7
    @11
    cE
    @10
    c.x
    oveq2
    @26
    @14
    @6
    cN
    @26
    @13
    @5
    cB
    @11
    cE
    sneq
    difeq2d
    fveq2d
    eleq12d
    notbid
    @10
    cA
    wceq
    #
    @25
    @8
    @27
    @24
    @4
    @7
    @10
    cA
    cE
    c.x
    oveq1
    eleq1d
    notbid
    rspc2v
    syl5com
    impl
    sylan2br
end
