include "clmod.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wss.mm"
include "crab.mm"
include "cuni.mm"
include "cfv.mm"
include "c0g.mm"
include "eleq1.mm"
include "wne.mm"
include "csn.mm"
include "wceq.mm"
include "simplll.mm"
include "cbs.mm"
include "simpllr.mm"
include "simplr.mm"
include "eqid.mm"
include "lssel.mm"
include "syl2anc.mm"
include "lspsncl.mm"
include "lspid.mm"
include "lsatlss.mm"
include "adantr.mm"
include "rabss2.mm"
include "uniss.mm"
include "3syl.mm"
include "unimax.mm"
include "lssss.mm"
include "eqsstrd.mm"
include "adantl.mm"
include "sstrd.mm"
include "ad2antrr.mm"
include "simpr.mm"
include "lsatlspsn2.mm"
include "syl3anc.mm"
include "lspsnel5a.mm"
include "sseq1.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "elssuni.mm"
include "syl.mm"
include "lspss.mm"
include "eqsstr3d.mm"
include "lspsnid.mm"
include "sseldd.mm"
include "simpll.mm"
include "lspcl.mm"
include "syldan.mm"
include "lss0cl.mm"
include "pm2.61ne.mm"
include "ex.mm"
include "ssrdv.mm"
include "simpl.mm"
include "fveq2d.mm"
include "eqtrd.mm"
include "sseqtrd.mm"
include "eqssd.mm"

theorem lssats
  let vx: setvar x
  let cA: class A
  let cS: class S
  let cU: class U
  let cN: class N
  let cW: class W
  let vy: setvar y
  assume lssats.s: |- S = ( LSubSp ` W )
  assume lssats.n: |- N = ( LSpan ` W )
  assume lssats.a: |- A = ( LSAtoms ` W )

  disjoint A x
  disjoint N x
  disjoint S x
  disjoint U x
  disjoint x y
  disjoint A y
  disjoint N y
  disjoint S y
  disjoint U y
  disjoint W y
  assert |- ( ( W e. LMod /\ U e. S ) -> U = ( N ` U. { x e. A | x C_ U } ) )

  proof
    cW
    clmod
    wcel
    #
    cU
    cS
    wcel
    #
    wa
    #
    cU
    vx
    cv
    #
    cU
    wss
    #
    vx
    cA
    crab
    #
    cuni
    #
    cN
    cfv
    #
    @2
    vy
    cU
    @7
    @2
    vy
    cv
    #
    cU
    wcel
    #
    @8
    @7
    wcel
    #
    @2
    @9
    wa
    #
    @10
    cW
    c0g
    cfv
    #
    @7
    wcel
    #
    @8
    @12
    @8
    @12
    @7
    eleq1
    @11
    @8
    @12
    wne
    #
    wa
    #
    @8
    csn
    cN
    cfv
    #
    @7
    @8
    @15
    @16
    @16
    cN
    cfv
    #
    @7
    @15
    @0
    @16
    cS
    wcel
    #
    @17
    @16
    wceq
    @0
    @1
    @9
    @14
    simplll
    #
    @15
    @0
    @8
    cW
    cbs
    cfv
    #
    wcel
    #
    @18
    @19
    @15
    @1
    @9
    @21
    @0
    @1
    @9
    @14
    simpllr
    #
    @2
    @9
    @14
    simplr
    #
    cS
    cU
    @20
    cW
    @8
    @20
    eqid
    #
    lssats.s
    lssel
    syl2anc
    #
    cS
    cN
    @20
    cW
    @8
    @24
    lssats.s
    lssats.n
    lspsncl
    syl2anc
    cS
    @16
    cN
    cW
    lssats.s
    lssats.n
    lspid
    syl2anc
    @15
    @0
    @6
    @20
    wss
    #
    @16
    @6
    wss
    #
    @17
    @7
    wss
    @19
    @2
    @26
    @9
    @14
    @2
    @6
    @4
    vx
    cS
    crab
    #
    cuni
    #
    @20
    @2
    cA
    cS
    wss
    #
    @5
    @28
    wss
    @6
    @29
    wss
    #
    @0
    @30
    @1
    cA
    cS
    cW
    lssats.s
    lssats.a
    lsatlss
    adantr
    @4
    vx
    cA
    cS
    rabss2
    @5
    @28
    uniss
    3syl
    #
    @1
    @29
    @20
    wss
    #
    @0
    @1
    @29
    cU
    @20
    vx
    cU
    cS
    unimax
    #
    cS
    cU
    @20
    cW
    @24
    lssats.s
    lssss
    eqsstrd
    adantl
    #
    sstrd
    #
    ad2antrr
    @15
    @16
    @5
    wcel
    #
    @27
    @15
    @16
    cA
    wcel
    #
    @16
    cU
    wss
    #
    @37
    @15
    @0
    @21
    @14
    @38
    @19
    @25
    @11
    @14
    simpr
    cA
    cN
    @20
    cW
    @8
    @12
    @24
    lssats.n
    @12
    eqid
    #
    lssats.a
    lsatlspsn2
    syl3anc
    @15
    cS
    cU
    cN
    cW
    @8
    lssats.s
    lssats.n
    @19
    @22
    @23
    lspsnel5a
    @4
    @39
    vx
    @16
    cA
    @3
    @16
    cU
    sseq1
    elrab
    sylanbrc
    @16
    @5
    elssuni
    syl
    @16
    @6
    cN
    @20
    cW
    @24
    lssats.n
    lspss
    syl3anc
    eqsstr3d
    @15
    @0
    @21
    @8
    @16
    wcel
    @19
    @25
    cN
    @20
    cW
    @8
    @24
    lssats.n
    lspsnid
    syl2anc
    sseldd
    @11
    @0
    @7
    cS
    wcel
    #
    @13
    @0
    @1
    @9
    simpll
    @2
    @41
    @9
    @0
    @1
    @26
    @41
    @36
    cS
    @6
    cN
    @20
    cW
    @24
    lssats.s
    lssats.n
    lspcl
    syldan
    adantr
    cS
    @7
    cW
    @12
    @40
    lssats.s
    lss0cl
    syl2anc
    pm2.61ne
    ex
    ssrdv
    @2
    @7
    @29
    cN
    cfv
    #
    cU
    @2
    @0
    @33
    @31
    @7
    @42
    wss
    @0
    @1
    simpl
    @35
    @32
    @6
    @29
    cN
    @20
    cW
    @24
    lssats.n
    lspss
    syl3anc
    @2
    @42
    cU
    cN
    cfv
    cU
    @2
    @29
    cU
    cN
    @1
    @29
    cU
    wceq
    @0
    @34
    adantl
    fveq2d
    cS
    cU
    cN
    cW
    lssats.s
    lssats.n
    lspid
    eqtrd
    sseqtrd
    eqssd
end
