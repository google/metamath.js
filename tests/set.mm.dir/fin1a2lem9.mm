include "crpss.mm"
include "wor.mm"
include "cfn.mm"
include "wss.mm"
include "com.mm"
include "wcel.mm"
include "w3a.mm"
include "csuc.mm"
include "cv.mm"
include "cdom.mm"
include "wbr.mm"
include "crab.mm"
include "con0.mm"
include "cin.mm"
include "onfin2.mm"
include "inss2.mm"
include "eqsstri.mm"
include "peano2.mm"
include "sseldi.mm"
include "3ad2ant3.mm"
include "ccrd.mm"
include "cfv.mm"
include "wa.mm"
include "breq1.mm"
include "elrab.mm"
include "simprr.mm"
include "cdm.mm"
include "wb.mm"
include "simpl2.mm"
include "simprl.mm"
include "sseldd.mm"
include "finnum.mm"
include "syl.mm"
include "simpl3.mm"
include "carddom2.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "ex.mm"
include "cardnn.mm"
include "sseq2d.mm"
include "cardon.mm"
include "nnon.mm"
include "onsssuc.mm"
include "sylancr.mm"
include "bitrd.mm"
include "sylibd.mm"
include "syl5bi.mm"
include "wceq.mm"
include "elrabi.mm"
include "wo.mm"
include "wi.mm"
include "ssel.mm"
include "anim12d.mm"
include "imp.mm"
include "3ad2antl2.mm"
include "sorpssi.mm"
include "3ad2antl1.mm"
include "cen.mm"
include "carden2.mm"
include "syl2an.mm"
include "adantr.mm"
include "fin23lem25.mm"
include "3expa.mm"
include "biimpd.mm"
include "sylbid.mm"
include "fveq2.mm"
include "impbid1.mm"
include "syl2ani.mm"
include "dom2d.mm"
include "mpd.mm"
include "domfi.mm"

theorem fin1a2lem9
  let cA: class A
  let cX: class X
  let vb: setvar b
  let va: setvar a
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cV: class V
  let cC: class C

  disjoint A b
  disjoint X b
  disjoint a b
  disjoint a c
  disjoint a d
  disjoint a e
  disjoint a f
  disjoint a g
  disjoint a h
  disjoint a x
  disjoint a y
  disjoint A a
  disjoint b c
  disjoint b d
  disjoint b e
  disjoint b f
  disjoint b g
  disjoint b h
  disjoint b x
  disjoint b y
  disjoint c d
  disjoint c e
  disjoint c f
  disjoint c g
  disjoint c h
  disjoint c x
  disjoint c y
  disjoint A c
  disjoint d e
  disjoint d f
  disjoint d g
  disjoint d h
  disjoint d x
  disjoint d y
  disjoint A d
  disjoint e f
  disjoint e g
  disjoint e h
  disjoint e x
  disjoint e y
  disjoint A e
  disjoint f g
  disjoint f h
  disjoint f x
  disjoint f y
  disjoint A f
  disjoint g h
  disjoint g x
  disjoint g y
  disjoint A g
  disjoint h x
  disjoint h y
  disjoint A h
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B d
  disjoint B e
  disjoint B f
  disjoint B g
  disjoint B h
  disjoint V c
  disjoint V x
  disjoint X c
  disjoint X d
  disjoint C e
  disjoint C f
  disjoint C g
  disjoint C h
  disjoint C x
  assert |- ( ( [C.] Or X /\ X C_ Fin /\ A e. _om ) -> { b e. X | b ~<_ A } e. Fin )

  proof
    cX
    crpss
    wor
    #
    cX
    cfn
    wss
    #
    cA
    com
    wcel
    #
    w3a
    #
    cA
    csuc
    #
    cfn
    wcel
    #
    vb
    cv
    #
    cA
    cdom
    wbr
    #
    vb
    cX
    crab
    #
    @4
    cdom
    wbr
    #
    @8
    cfn
    wcel
    @2
    @0
    @5
    @1
    @2
    com
    cfn
    @4
    com
    con0
    cfn
    cin
    cfn
    onfin2
    con0
    cfn
    inss2
    eqsstri
    #
    cA
    peano2
    #
    sseldi
    3ad2ant3
    @3
    @4
    com
    wcel
    #
    @9
    @2
    @0
    @12
    @1
    @11
    3ad2ant3
    @3
    vc
    vd
    @8
    @4
    vc
    cv
    #
    ccrd
    cfv
    #
    vd
    cv
    #
    ccrd
    cfv
    #
    com
    @13
    @8
    wcel
    #
    @13
    cX
    wcel
    #
    @13
    cA
    cdom
    wbr
    #
    wa
    #
    @3
    @14
    @4
    wcel
    #
    @7
    @19
    vb
    @13
    cX
    @6
    @13
    cA
    cdom
    breq1
    elrab
    @3
    @20
    @14
    cA
    ccrd
    cfv
    #
    wss
    #
    @21
    @3
    @20
    @23
    @3
    @20
    wa
    #
    @23
    @19
    @3
    @18
    @19
    simprr
    @24
    @13
    ccrd
    cdm
    #
    wcel
    #
    cA
    @25
    wcel
    #
    @23
    @19
    wb
    @24
    @13
    cfn
    wcel
    #
    @26
    @24
    cX
    cfn
    @13
    @0
    @1
    @2
    @20
    simpl2
    @3
    @18
    @19
    simprl
    sseldd
    @13
    finnum
    #
    syl
    @24
    cA
    cfn
    wcel
    @27
    @24
    com
    cfn
    cA
    @10
    @0
    @1
    @2
    @20
    simpl3
    sseldi
    cA
    finnum
    syl
    @13
    cA
    carddom2
    syl2anc
    mpbird
    ex
    @2
    @0
    @23
    @21
    wb
    @1
    @2
    @23
    @14
    cA
    wss
    #
    @21
    @2
    @22
    cA
    @14
    cA
    cardnn
    sseq2d
    @2
    @14
    con0
    wcel
    cA
    con0
    wcel
    @30
    @21
    wb
    @13
    cardon
    cA
    nnon
    @14
    cA
    onsssuc
    sylancr
    bitrd
    3ad2ant3
    sylibd
    syl5bi
    @17
    @3
    @18
    @15
    cX
    wcel
    #
    @14
    @16
    wceq
    #
    @13
    @15
    wceq
    #
    wb
    #
    @15
    @8
    wcel
    @7
    vb
    @13
    cX
    elrabi
    @7
    vb
    @15
    cX
    elrabi
    @3
    @18
    @31
    wa
    #
    @34
    @3
    @35
    wa
    #
    @32
    @33
    @36
    @28
    @15
    cfn
    wcel
    #
    wa
    #
    @13
    @15
    wss
    @15
    @13
    wss
    wo
    #
    @32
    @33
    wi
    @1
    @0
    @35
    @38
    @2
    @1
    @35
    @38
    @1
    @18
    @28
    @31
    @37
    cX
    cfn
    @13
    ssel
    cX
    cfn
    @15
    ssel
    anim12d
    imp
    3ad2antl2
    @0
    @1
    @35
    @39
    @2
    cX
    @13
    @15
    sorpssi
    3ad2antl1
    @38
    @39
    wa
    #
    @32
    @13
    @15
    cen
    wbr
    #
    @33
    @38
    @32
    @41
    wb
    #
    @39
    @28
    @26
    @15
    @25
    wcel
    @42
    @37
    @29
    @15
    finnum
    @13
    @15
    carden2
    syl2an
    adantr
    @40
    @41
    @33
    @28
    @37
    @39
    @41
    @33
    wb
    @13
    @15
    fin23lem25
    3expa
    biimpd
    sylbid
    syl2anc
    @13
    @15
    ccrd
    fveq2
    impbid1
    ex
    syl2ani
    dom2d
    mpd
    @4
    @8
    domfi
    syl2anc
end
