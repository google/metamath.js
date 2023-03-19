include "wcel.mm"
include "cec.mm"
include "cfv.mm"
include "creverse.mm"
include "ccom.mm"
include "wceq.mm"
include "cplusg.mm"
include "co.mm"
include "c0g.mm"
include "cconcat.mm"
include "c0.mm"
include "c2o.mm"
include "cxp.mm"
include "cword.mm"
include "wf.mm"
include "cid.mm"
include "fviss.mm"
include "eqsstri.mm"
include "sseli.mm"
include "revcl.mm"
include "syl.mm"
include "efgmf.mm"
include "wrdco.mm"
include "sylancl.mm"
include "cvv.mm"
include "efgrcl.mm"
include "simprd.mm"
include "eleqtrrd.mm"
include "eqid.mm"
include "frgpadd.mm"
include "mpdan.mm"
include "wer.mm"
include "efger.mm"
include "a1i.mm"
include "cc0.mm"
include "cv.mm"
include "chash.mm"
include "cfz.mm"
include "cs2.mm"
include "cotp.mm"
include "csplice.mm"
include "cmpt2.mm"
include "cmpt.mm"
include "efginvrel2.mm"
include "erthi.mm"
include "cgrp.mm"
include "wa.mm"
include "frgp0.mm"
include "adantr.mm"
include "3eqtrd.mm"
include "cbs.mm"
include "wb.mm"
include "simpld.mm"
include "frgpeccl.mm"
include "grpinvid1.mm"
include "syl3anc.mm"
include "mpbird.mm"

theorem frgpinv
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let c.sm: class .~
  let cG: class G
  let cI: class I
  let cM: class M
  let cN: class N
  let cW: class W
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let vn: setvar n
  let vv: setvar v
  let vw: setvar w
  let cB: class B
  let c.pl: class .+
  assume frgpadd.w: |- W = ( _I ` Word ( I X. 2o ) )
  assume frgpadd.g: |- G = ( freeGrp ` I )
  assume frgpadd.r: |- .~ = ( ~FG ` I )
  assume frgpinv.n: |- N = ( invg ` G )
  assume frgpinv.m: |- M = ( y e. I , z e. 2o |-> <. y , ( 1o \ z ) >. )

  disjoint y z
  disjoint I y
  disjoint I z
  disjoint .~ y
  disjoint .~ z
  disjoint W y
  disjoint W z
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint A a
  disjoint b c
  disjoint b d
  disjoint A b
  disjoint c d
  disjoint A c
  disjoint A d
  disjoint b n
  disjoint b v
  disjoint b w
  disjoint b y
  disjoint b z
  disjoint I b
  disjoint d n
  disjoint d v
  disjoint d w
  disjoint d y
  disjoint d z
  disjoint I d
  disjoint n v
  disjoint n w
  disjoint n y
  disjoint n z
  disjoint I n
  disjoint v w
  disjoint v y
  disjoint v z
  disjoint I v
  disjoint w y
  disjoint w z
  disjoint I w
  disjoint M n
  disjoint M v
  disjoint M w
  disjoint a y
  disjoint a z
  disjoint .~ a
  disjoint .~ b
  disjoint c y
  disjoint c z
  disjoint .~ c
  disjoint .~ d
  disjoint B a
  disjoint B b
  disjoint B c
  disjoint B d
  disjoint .+ a
  disjoint .+ b
  disjoint .+ c
  disjoint .+ d
  disjoint a n
  disjoint a v
  disjoint a w
  disjoint W a
  disjoint W b
  disjoint c n
  disjoint c v
  disjoint c w
  disjoint W c
  disjoint W d
  disjoint W n
  disjoint W v
  disjoint W w
  assert |- ( A e. W -> ( N ` [ A ] .~ ) = [ ( M o. ( reverse ` A ) ) ] .~ )

  proof
    cA
    cW
    wcel
    #
    cA
    c.sm
    cec
    #
    cN
    cfv
    cM
    cA
    creverse
    cfv
    #
    ccom
    #
    c.sm
    cec
    #
    wceq
    #
    @1
    @4
    cG
    cplusg
    cfv
    #
    co
    #
    cG
    c0g
    cfv
    #
    wceq
    #
    @0
    @7
    cA
    @3
    cconcat
    co
    #
    c.sm
    cec
    #
    c0
    c.sm
    cec
    #
    @8
    @0
    @3
    cW
    wcel
    #
    @7
    @11
    wceq
    @0
    @3
    cI
    c2o
    cxp
    #
    cword
    #
    cW
    @0
    @2
    @15
    wcel
    #
    @14
    @14
    cM
    wf
    @3
    @15
    wcel
    @0
    cA
    @15
    wcel
    @16
    cW
    @15
    cA
    cW
    @15
    cid
    cfv
    @15
    frgpadd.w
    @15
    fviss
    eqsstri
    sseli
    @14
    cA
    revcl
    syl
    vy
    vz
    cI
    cM
    frgpinv.m
    efgmf
    @14
    @14
    cM
    @2
    wrdco
    sylancl
    @0
    cI
    cvv
    wcel
    #
    cW
    @15
    wceq
    #
    cA
    cI
    cW
    frgpadd.w
    efgrcl
    #
    simprd
    eleqtrrd
    #
    cA
    @3
    @6
    c.sm
    cG
    cI
    cW
    frgpadd.w
    frgpadd.g
    frgpadd.r
    @6
    eqid
    #
    frgpadd
    mpdan
    @0
    @10
    c0
    c.sm
    cW
    cW
    c.sm
    wer
    @0
    c.sm
    cI
    cW
    frgpadd.w
    frgpadd.r
    efger
    a1i
    vy
    vz
    vw
    vv
    cA
    c.sm
    vv
    cW
    vn
    vw
    cc0
    vv
    cv
    #
    chash
    cfv
    cfz
    co
    @14
    @22
    vn
    cv
    #
    @23
    vw
    cv
    #
    @24
    cM
    cfv
    cs2
    cotp
    csplice
    co
    cmpt2
    cmpt
    #
    vn
    cI
    cM
    cW
    frgpadd.w
    frgpadd.r
    frgpinv.m
    @25
    eqid
    efginvrel2
    erthi
    @0
    cG
    cgrp
    wcel
    #
    @12
    @8
    wceq
    #
    @0
    @17
    @18
    wa
    @26
    @27
    wa
    #
    @19
    @17
    @28
    @18
    c.sm
    cG
    cI
    cvv
    frgpadd.g
    frgpadd.r
    frgp0
    adantr
    syl
    #
    simprd
    3eqtrd
    @0
    @26
    @1
    cG
    cbs
    cfv
    #
    wcel
    @4
    @30
    wcel
    #
    @5
    @9
    wb
    @0
    @26
    @27
    @29
    simpld
    @30
    c.sm
    cG
    cI
    cW
    cA
    frgpadd.g
    frgpadd.r
    frgpadd.w
    @30
    eqid
    #
    frgpeccl
    @0
    @13
    @31
    @20
    @30
    c.sm
    cG
    cI
    cW
    @3
    frgpadd.g
    frgpadd.r
    frgpadd.w
    @32
    frgpeccl
    syl
    @30
    @6
    cG
    cN
    @1
    @4
    @8
    @32
    @21
    @8
    eqid
    frgpinv.n
    grpinvid1
    syl3anc
    mpbird
end
