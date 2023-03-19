include "clinds.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "wne.mm"
include "csn.mm"
include "cdif.mm"
include "cv.mm"
include "co.mm"
include "wn.mm"
include "wral.mm"
include "simplr.mm"
include "eldifsn.mm"
include "biimpri.mm"
include "adantl.mm"
include "cbs.mm"
include "wss.mm"
include "cdm.mm"
include "wb.mm"
include "elfvdm.mm"
include "eqid.mm"
include "islinds2.mm"
include "syl.mm"
include "ibi.mm"
include "simprd.mm"
include "ad2antrr.mm"
include "wceq.mm"
include "oveq2.mm"
include "sneq.mm"
include "difeq2d.mm"
include "fveq2d.mm"
include "eleq12d.mm"
include "notbid.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "rspc2va.mm"
include "syl21anc.mm"

theorem lindsind
  let cA: class A
  let c.x: class .x.
  let cE: class E
  let cF: class F
  let cK: class K
  let cL: class L
  let cN: class N
  let cW: class W
  let c.0: class .0.
  let va: setvar a
  let ve: setvar e
  assume lindfind.s: |- .x. = ( .s ` W )
  assume lindfind.n: |- N = ( LSpan ` W )
  assume lindfind.l: |- L = ( Scalar ` W )
  assume lindfind.z: |- .0. = ( 0g ` L )
  assume lindfind.k: |- K = ( Base ` L )


  assert |- ( ( ( F e. ( LIndS ` W ) /\ E e. F ) /\ ( A e. K /\ A =/= .0. ) ) -> -. ( A .x. E ) e. ( N ` ( F \ { E } ) ) )

  proof
    cF
    cW
    clinds
    cfv
    wcel
    #
    cE
    cF
    wcel
    #
    wa
    #
    cA
    cK
    wcel
    cA
    c.0
    wne
    wa
    #
    wa
    @1
    cA
    cK
    c.0
    csn
    cdif
    #
    wcel
    #
    va
    cv
    #
    ve
    cv
    #
    c.x
    co
    #
    cF
    @7
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
    va
    @4
    wral
    ve
    cF
    wral
    #
    cA
    cE
    c.x
    co
    #
    cF
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
    @0
    @1
    @3
    simplr
    @3
    @5
    @2
    @5
    @3
    cA
    cK
    c.0
    eldifsn
    biimpri
    adantl
    @0
    @14
    @1
    @3
    @0
    cF
    cW
    cbs
    cfv
    #
    wss
    #
    @14
    @0
    @22
    @14
    wa
    #
    @0
    cW
    clinds
    cdm
    #
    wcel
    @0
    @23
    wb
    cF
    cW
    clinds
    elfvdm
    ve
    @21
    cL
    c.x
    va
    cF
    cN
    cK
    cW
    @24
    c.0
    @21
    eqid
    lindfind.s
    lindfind.n
    lindfind.l
    lindfind.k
    lindfind.z
    islinds2
    syl
    ibi
    simprd
    ad2antrr
    @13
    @20
    @6
    cE
    c.x
    co
    #
    @18
    wcel
    #
    wn
    ve
    va
    cE
    cA
    cF
    @4
    @7
    cE
    wceq
    #
    @12
    @26
    @27
    @8
    @25
    @11
    @18
    @7
    cE
    @6
    c.x
    oveq2
    @27
    @10
    @17
    cN
    @27
    @9
    @16
    cF
    @7
    cE
    sneq
    difeq2d
    fveq2d
    eleq12d
    notbid
    @6
    cA
    wceq
    #
    @26
    @19
    @28
    @25
    @15
    @18
    @6
    cA
    cE
    c.x
    oveq1
    eleq1d
    notbid
    rspc2va
    syl21anc
end
