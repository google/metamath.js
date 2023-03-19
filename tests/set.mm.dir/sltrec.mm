include "csslt.mm"
include "wbr.mm"
include "wa.mm"
include "cscut.mm"
include "co.mm"
include "wceq.mm"
include "cslt.mm"
include "cv.mm"
include "csle.mm"
include "wrex.mm"
include "wo.mm"
include "wral.mm"
include "wn.mm"
include "wb.mm"
include "simplr.mm"
include "simpll.mm"
include "simprr.mm"
include "simprl.mm"
include "slerec.mm"
include "syl22anc.mm"
include "ancom.mm"
include "syl6bb.mm"
include "csur.mm"
include "wcel.mm"
include "csn.mm"
include "scutcut.mm"
include "simp1d.mm"
include "ad2antlr.mm"
include "eqeltrd.mm"
include "ad2antrr.mm"
include "slenlt.mm"
include "syl2anc.mm"
include "wss.mm"
include "ssltss1.mm"
include "sselda.mm"
include "adantr.mm"
include "sltnle.mm"
include "ralbidva.mm"
include "ssltss2.mm"
include "anbi12d.mm"
include "ralnex.mm"
include "anbi12i.mm"
include "ioran.mm"
include "bitr4i.mm"
include "3bitr3d.mm"
include "con4bid.mm"

theorem sltrec
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cX: class X
  let cY: class Y
  let vb: setvar b
  let vc: setvar c

  disjoint A b
  disjoint A c
  disjoint b c
  disjoint B b
  disjoint B c
  disjoint C b
  disjoint C c
  disjoint D b
  disjoint D c
  disjoint X b
  disjoint X c
  disjoint Y b
  disjoint Y c
  assert |- ( ( ( A <<s B /\ C <<s D ) /\ ( X = ( A |s B ) /\ Y = ( C |s D ) ) ) -> ( X <s Y <-> ( E. c e. C X <_s c \/ E. b e. B b <_s Y ) ) )

  proof
    cA
    cB
    csslt
    wbr
    #
    cC
    cD
    csslt
    wbr
    #
    wa
    #
    cX
    cA
    cB
    cscut
    co
    #
    wceq
    #
    cY
    cC
    cD
    cscut
    co
    #
    wceq
    #
    wa
    #
    wa
    #
    cX
    cY
    cslt
    wbr
    #
    cX
    vc
    cv
    #
    csle
    wbr
    #
    vc
    cC
    wrex
    #
    vb
    cv
    #
    cY
    csle
    wbr
    #
    vb
    cB
    wrex
    #
    wo
    #
    @8
    cY
    cX
    csle
    wbr
    #
    @10
    cX
    cslt
    wbr
    #
    vc
    cC
    wral
    #
    cY
    @13
    cslt
    wbr
    #
    vb
    cB
    wral
    #
    wa
    #
    @9
    wn
    #
    @16
    wn
    #
    @8
    @17
    @21
    @19
    wa
    #
    @22
    @8
    @1
    @0
    @6
    @4
    @17
    @25
    wb
    @0
    @1
    @7
    simplr
    @0
    @1
    @7
    simpll
    @2
    @4
    @6
    simprr
    #
    @2
    @4
    @6
    simprl
    #
    cC
    cD
    cA
    cB
    cY
    cX
    vc
    vb
    slerec
    syl22anc
    @21
    @19
    ancom
    syl6bb
    @8
    cY
    csur
    wcel
    #
    cX
    csur
    wcel
    #
    @17
    @23
    wb
    @8
    cY
    @5
    csur
    @26
    @1
    @5
    csur
    wcel
    #
    @0
    @7
    @1
    @30
    cC
    @5
    csn
    #
    csslt
    wbr
    @31
    cD
    csslt
    wbr
    cC
    cD
    scutcut
    simp1d
    ad2antlr
    eqeltrd
    #
    @8
    cX
    @3
    csur
    @27
    @0
    @3
    csur
    wcel
    #
    @1
    @7
    @0
    @33
    cA
    @3
    csn
    #
    csslt
    wbr
    @34
    cB
    csslt
    wbr
    cA
    cB
    scutcut
    simp1d
    ad2antrr
    eqeltrd
    #
    cY
    cX
    slenlt
    syl2anc
    @8
    @22
    @11
    wn
    #
    vc
    cC
    wral
    #
    @14
    wn
    #
    vb
    cB
    wral
    #
    wa
    #
    @24
    @8
    @19
    @37
    @21
    @39
    @8
    @18
    @36
    vc
    cC
    @8
    @10
    cC
    wcel
    #
    wa
    @10
    csur
    wcel
    @29
    @18
    @36
    wb
    @8
    cC
    csur
    @10
    @1
    cC
    csur
    wss
    @0
    @7
    cC
    cD
    ssltss1
    ad2antlr
    sselda
    @8
    @29
    @41
    @35
    adantr
    @10
    cX
    sltnle
    syl2anc
    ralbidva
    @8
    @20
    @38
    vb
    cB
    @8
    @13
    cB
    wcel
    #
    wa
    @28
    @13
    csur
    wcel
    @20
    @38
    wb
    @8
    @28
    @42
    @32
    adantr
    @8
    cB
    csur
    @13
    @0
    cB
    csur
    wss
    @1
    @7
    cA
    cB
    ssltss2
    ad2antrr
    sselda
    cY
    @13
    sltnle
    syl2anc
    ralbidva
    anbi12d
    @40
    @12
    wn
    #
    @15
    wn
    #
    wa
    @24
    @37
    @43
    @39
    @44
    @11
    vc
    cC
    ralnex
    @14
    vb
    cB
    ralnex
    anbi12i
    @12
    @15
    ioran
    bitr4i
    syl6bb
    3bitr3d
    con4bid
end
