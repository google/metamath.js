include "wcel.mm"
include "wral.mm"
include "wa.mm"
include "cpw.mm"
include "cin.mm"
include "cv.mm"
include "csn.mm"
include "wss.mm"
include "wi.mm"
include "crab.mm"
include "ciin.mm"
include "cacs.mm"
include "cfv.mm"
include "riinrab.mm"
include "wb.mm"
include "elpwi.mm"
include "ssrin.mm"
include "syl.mm"
include "adantl.mm"
include "ralss.mm"
include "inss2.mm"
include "sseli.mm"
include "biantrud.mm"
include "vex.mm"
include "snss.mm"
include "bicomi.mm"
include "elin.mm"
include "3bitr4g.mm"
include "imbi1d.mm"
include "ralbiia.mm"
include "syl6rbbr.mm"
include "rabbidva.mm"
include "syl5eq.mm"
include "cmre.mm"
include "mreacs.mm"
include "adantr.mm"
include "ssralv.mm"
include "ax-mp.mm"
include "cfn.mm"
include "simpll.mm"
include "simpr.mm"
include "inss1.mm"
include "ad2antlr.mm"
include "snssd.mm"
include "snfi.mm"
include "a1i.mm"
include "acsfn.mm"
include "syl22anc.mm"
include "ex.mm"
include "ralimdva.mm"
include "syl5.mm"
include "imp.mm"
include "mreriincl.mm"
include "syl2anc.mm"
include "eqeltrrd.mm"

theorem acsfn1p
  let cE: class E
  let cV: class V
  let cX: class X
  let cY: class Y
  let va: setvar a
  let vb: setvar b

  disjoint a b
  disjoint V a
  disjoint V b
  disjoint E a
  disjoint X a
  disjoint X b
  disjoint Y a
  disjoint Y b
  assert |- ( ( X e. V /\ A. b e. Y E e. X ) -> { a e. ~P X | A. b e. ( a i^i Y ) E e. a } e. ( ACS ` X ) )

  proof
    cX
    cV
    wcel
    #
    cE
    cX
    wcel
    #
    vb
    cY
    wral
    #
    wa
    #
    cX
    cpw
    #
    vb
    cX
    cY
    cin
    #
    vb
    cv
    #
    csn
    #
    va
    cv
    #
    wss
    #
    cE
    @8
    wcel
    #
    wi
    #
    va
    @4
    crab
    #
    ciin
    cin
    #
    @10
    vb
    @8
    cY
    cin
    #
    wral
    #
    va
    @4
    crab
    #
    cX
    cacs
    cfv
    #
    @3
    @13
    @11
    vb
    @5
    wral
    #
    va
    @4
    crab
    @16
    @11
    vb
    va
    @4
    @5
    riinrab
    @3
    @18
    @15
    va
    @4
    @3
    @8
    @4
    wcel
    #
    wa
    #
    @15
    @6
    @14
    wcel
    #
    @10
    wi
    #
    vb
    @5
    wral
    #
    @18
    @20
    @14
    @5
    wss
    #
    @15
    @23
    wb
    @19
    @24
    @3
    @19
    @8
    cX
    wss
    @24
    @8
    cX
    elpwi
    @8
    cX
    cY
    ssrin
    syl
    adantl
    @10
    vb
    @14
    @5
    ralss
    syl
    @11
    @22
    vb
    @5
    @6
    @5
    wcel
    #
    @9
    @21
    @10
    @25
    @6
    @8
    wcel
    #
    @26
    @6
    cY
    wcel
    #
    wa
    @9
    @21
    @25
    @27
    @26
    @5
    cY
    @6
    cX
    cY
    inss2
    #
    sseli
    biantrud
    @26
    @9
    @6
    @8
    vb
    vex
    snss
    bicomi
    @6
    @8
    cY
    elin
    3bitr4g
    imbi1d
    ralbiia
    syl6rbbr
    rabbidva
    syl5eq
    @3
    @17
    @4
    cmre
    cfv
    wcel
    #
    @12
    @17
    wcel
    #
    vb
    @5
    wral
    #
    @13
    @17
    wcel
    @0
    @29
    @2
    cV
    cX
    mreacs
    adantr
    @0
    @2
    @31
    @2
    @1
    vb
    @5
    wral
    #
    @0
    @31
    @5
    cY
    wss
    @2
    @32
    wi
    @28
    @1
    vb
    @5
    cY
    ssralv
    ax-mp
    @0
    @1
    @30
    vb
    @5
    @0
    @25
    wa
    #
    @1
    @30
    @33
    @1
    wa
    #
    @0
    @1
    @7
    cX
    wss
    @7
    cfn
    wcel
    #
    @30
    @0
    @25
    @1
    simpll
    @33
    @1
    simpr
    @34
    @6
    cX
    @25
    @6
    cX
    wcel
    @0
    @1
    @5
    cX
    @6
    cX
    cY
    inss1
    sseli
    ad2antlr
    snssd
    @35
    @34
    @6
    snfi
    a1i
    @7
    cE
    cV
    cX
    va
    acsfn
    syl22anc
    ex
    ralimdva
    syl5
    imp
    vb
    @17
    @12
    @5
    @4
    mreriincl
    syl2anc
    eqeltrrd
end
