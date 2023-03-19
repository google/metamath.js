include "clindf.mm"
include "wbr.mm"
include "cdm.mm"
include "wcel.mm"
include "wa.mm"
include "wne.mm"
include "csn.mm"
include "cdif.mm"
include "cv.mm"
include "cfv.mm"
include "co.mm"
include "cima.mm"
include "wn.mm"
include "wral.mm"
include "simplr.mm"
include "eldifsn.mm"
include "biimpri.mm"
include "adantl.mm"
include "cbs.mm"
include "wf.mm"
include "simpll.mm"
include "cvv.mm"
include "wb.mm"
include "csca.mm"
include "elbasfv.mm"
include "ad2antrl.mm"
include "rellindf.mm"
include "brrelexi.mm"
include "ad2antrr.mm"
include "eqid.mm"
include "islindf.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "simprd.mm"
include "wceq.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "sneq.mm"
include "difeq2d.mm"
include "imaeq2d.mm"
include "fveq2d.mm"
include "eleq12d.mm"
include "notbid.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "rspc2va.mm"
include "syl21anc.mm"

theorem lindfind
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


  assert |- ( ( ( F LIndF W /\ E e. dom F ) /\ ( A e. K /\ A =/= .0. ) ) -> -. ( A .x. ( F ` E ) ) e. ( N ` ( F " ( dom F \ { E } ) ) ) )

  proof
    cF
    cW
    clindf
    wbr
    #
    cE
    cF
    cdm
    #
    wcel
    #
    wa
    #
    cA
    cK
    wcel
    #
    cA
    c.0
    wne
    #
    wa
    #
    wa
    #
    @2
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
    cF
    cfv
    #
    c.x
    co
    #
    cF
    @1
    @11
    csn
    #
    cdif
    #
    cima
    #
    cN
    cfv
    #
    wcel
    #
    wn
    #
    va
    @8
    wral
    ve
    @1
    wral
    #
    cA
    cE
    cF
    cfv
    #
    c.x
    co
    #
    cF
    @1
    cE
    csn
    #
    cdif
    #
    cima
    #
    cN
    cfv
    #
    wcel
    #
    wn
    #
    @0
    @2
    @6
    simplr
    @6
    @9
    @3
    @9
    @6
    cA
    cK
    c.0
    eldifsn
    biimpri
    adantl
    @7
    @1
    cW
    cbs
    cfv
    #
    cF
    wf
    #
    @20
    @7
    @0
    @30
    @20
    wa
    #
    @0
    @2
    @6
    simpll
    @7
    cW
    cvv
    wcel
    #
    cF
    cvv
    wcel
    #
    @0
    @31
    wb
    @4
    @32
    @3
    @5
    cK
    cL
    csca
    cA
    cW
    lindfind.l
    lindfind.k
    elbasfv
    ad2antrl
    @0
    @33
    @2
    @6
    cF
    cW
    clindf
    rellindf
    brrelexi
    ad2antrr
    ve
    @29
    cL
    c.x
    va
    cF
    cN
    cK
    cW
    cvv
    cvv
    c.0
    @29
    eqid
    lindfind.s
    lindfind.n
    lindfind.l
    lindfind.k
    lindfind.z
    islindf
    syl2anc
    mpbid
    simprd
    @19
    @28
    @10
    @21
    c.x
    co
    #
    @26
    wcel
    #
    wn
    ve
    va
    cE
    cA
    @1
    @8
    @11
    cE
    wceq
    #
    @18
    @35
    @36
    @13
    @34
    @17
    @26
    @36
    @12
    @21
    @10
    c.x
    @11
    cE
    cF
    fveq2
    oveq2d
    @36
    @16
    @25
    cN
    @36
    @15
    @24
    cF
    @36
    @14
    @23
    @1
    @11
    cE
    sneq
    difeq2d
    imaeq2d
    fveq2d
    eleq12d
    notbid
    @10
    cA
    wceq
    #
    @35
    @27
    @37
    @34
    @22
    @26
    @10
    cA
    @21
    c.x
    oveq1
    eleq1d
    notbid
    rspc2va
    syl21anc
end
