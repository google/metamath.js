include "wceq.mm"
include "cref.mm"
include "wbr.mm"
include "cv.mm"
include "wss.mm"
include "cfne.mm"
include "wa.mm"
include "wex.mm"
include "cun.mm"
include "cvv.mm"
include "wcel.mm"
include "refrel.mm"
include "brrelex2i.mm"
include "adantl.mm"
include "brrelexi.mm"
include "unexg.mm"
include "syl2anc.mm"
include "ssun2.mm"
include "a1i.mm"
include "ssun1.mm"
include "eqimss2.mm"
include "adantr.mm"
include "ssequn2.mm"
include "sylib.mm"
include "eqcomd.mm"
include "cuni.mm"
include "uneq12i.mm"
include "uniun.mm"
include "eqtr4i.mm"
include "fness.mm"
include "syl3anc.mm"
include "wrex.mm"
include "wral.mm"
include "wo.mm"
include "elun.mm"
include "wi.mm"
include "ssid.mm"
include "sseq2.mm"
include "rspcev.mm"
include "mpan2.mm"
include "refssex.mm"
include "ex.mm"
include "jaod.mm"
include "syl5bi.mm"
include "ralrimiv.mm"
include "wb.mm"
include "isref.mm"
include "syl.mm"
include "mpbir2and.mm"
include "jca32.mm"
include "breq2.mm"
include "breq1.mm"
include "anbi12d.mm"
include "spcegv.mm"
include "sylc.mm"
include "vex.mm"
include "ssex.mm"
include "ad2antrl.mm"
include "simprl.mm"
include "simpl.mm"
include "eqid.mm"
include "refbas.mm"
include "ad2antll.mm"
include "eqtr3d.mm"
include "ssref.mm"
include "simprrr.mm"
include "reftr.mm"
include "exlimdv.mm"
include "impbid.mm"

theorem refssfne
  let cA: class A
  let cB: class B
  let cX: class X
  let cY: class Y
  let vc: setvar c
  let vx: setvar x
  let vy: setvar y
  assume refssfne.1: |- X = U. A
  assume refssfne.2: |- Y = U. B

  disjoint A c
  disjoint B c
  disjoint X c
  disjoint Y c
  disjoint c x
  disjoint c y
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B x
  disjoint B y
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  assert |- ( X = Y -> ( B Ref A <-> E. c ( B C_ c /\ ( A Fne c /\ c Ref A ) ) ) )

  proof
    cX
    cY
    wceq
    #
    cB
    cA
    cref
    wbr
    #
    cB
    vc
    cv
    #
    wss
    #
    cA
    @2
    cfne
    wbr
    #
    @2
    cA
    cref
    wbr
    #
    wa
    #
    wa
    #
    vc
    wex
    #
    @0
    @1
    @8
    @0
    @1
    wa
    #
    cA
    cB
    cun
    #
    cvv
    wcel
    #
    cB
    @10
    wss
    #
    cA
    @10
    cfne
    wbr
    #
    @10
    cA
    cref
    wbr
    #
    wa
    #
    wa
    #
    @8
    @9
    cA
    cvv
    wcel
    #
    cB
    cvv
    wcel
    #
    @11
    @1
    @17
    @0
    cB
    cA
    cref
    refrel
    brrelex2i
    adantl
    @1
    @18
    @0
    cB
    cA
    cref
    refrel
    brrelexi
    adantl
    cA
    cB
    cvv
    cvv
    unexg
    syl2anc
    #
    @9
    @12
    @13
    @14
    @12
    @9
    cB
    cA
    ssun2
    a1i
    @9
    @11
    cA
    @10
    wss
    #
    cX
    cX
    cY
    cun
    #
    wceq
    #
    @13
    @19
    @20
    @9
    cA
    cB
    ssun1
    a1i
    @9
    @21
    cX
    @9
    cY
    cX
    wss
    #
    @21
    cX
    wceq
    @0
    @23
    @1
    cY
    cX
    eqimss2
    adantr
    cY
    cX
    ssequn2
    sylib
    eqcomd
    #
    cA
    @10
    cvv
    cX
    @21
    refssfne.1
    @21
    cA
    cuni
    #
    cB
    cuni
    #
    cun
    @10
    cuni
    cX
    @25
    cY
    @26
    refssfne.1
    refssfne.2
    uneq12i
    cA
    cB
    uniun
    eqtr4i
    #
    fness
    syl3anc
    @9
    @14
    @22
    vx
    cv
    #
    vy
    cv
    #
    wss
    #
    vy
    cA
    wrex
    #
    vx
    @10
    wral
    #
    @24
    @9
    @31
    vx
    @10
    @28
    @10
    wcel
    @28
    cA
    wcel
    #
    @28
    cB
    wcel
    #
    wo
    @9
    @31
    @28
    cA
    cB
    elun
    @9
    @33
    @31
    @34
    @33
    @31
    wi
    @9
    @33
    @28
    @28
    wss
    #
    @31
    @28
    ssid
    @30
    @35
    vy
    @28
    cA
    @29
    @28
    @28
    sseq2
    rspcev
    mpan2
    a1i
    @1
    @34
    @31
    wi
    @0
    @1
    @34
    @31
    vy
    cB
    cA
    @28
    refssex
    ex
    adantl
    jaod
    syl5bi
    ralrimiv
    @9
    @11
    @14
    @22
    @32
    wa
    wb
    @19
    vx
    vy
    @10
    cA
    cvv
    @21
    cX
    @27
    refssfne.1
    isref
    syl
    mpbir2and
    jca32
    @7
    @16
    vc
    @10
    cvv
    @2
    @10
    wceq
    #
    @3
    @12
    @6
    @15
    @2
    @10
    cB
    sseq2
    @36
    @4
    @13
    @5
    @14
    @2
    @10
    cA
    cfne
    breq2
    @2
    @10
    cA
    cref
    breq1
    anbi12d
    anbi12d
    spcegv
    sylc
    ex
    @0
    @7
    @1
    vc
    @0
    @7
    @1
    @0
    @7
    wa
    #
    cB
    @2
    cref
    wbr
    #
    @5
    @1
    @37
    @18
    @3
    cY
    @2
    cuni
    #
    wceq
    @38
    @3
    @18
    @0
    @6
    cB
    @2
    vc
    vex
    ssex
    ad2antrl
    @0
    @3
    @6
    simprl
    @37
    cX
    cY
    @39
    @0
    @7
    simpl
    @6
    cX
    @39
    wceq
    #
    @0
    @3
    @5
    @40
    @4
    @2
    cA
    @39
    cX
    @39
    eqid
    #
    refssfne.1
    refbas
    adantl
    ad2antll
    eqtr3d
    cB
    @2
    cvv
    cY
    @39
    refssfne.2
    @41
    ssref
    syl3anc
    @0
    @3
    @4
    @5
    simprrr
    cB
    @2
    cA
    reftr
    syl2anc
    ex
    exlimdv
    impbid
end
