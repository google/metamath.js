include "wiso.mm"
include "cv.mm"
include "wbr.mm"
include "wn.mm"
include "wa.mm"
include "wi.mm"
include "wral.mm"
include "wpo.mm"
include "wcel.mm"
include "w3a.mm"
include "cfv.mm"
include "wf1o.mm"
include "wf.mm"
include "isof1o.mm"
include "f1of.mm"
include "ffvelrn.mm"
include "ex.mm"
include "3anim123d.mm"
include "3syl.mm"
include "imp.mm"
include "wceq.mm"
include "wb.mm"
include "breq12.mm"
include "anidms.mm"
include "notbid.mm"
include "breq1.mm"
include "anbi1d.mm"
include "imbi12d.mm"
include "anbi12d.mm"
include "breq2.mm"
include "imbi1d.mm"
include "anbi2d.mm"
include "rspc3v.mm"
include "syl.mm"
include "simpl.mm"
include "simpr1.mm"
include "isorel.mm"
include "syl12anc.mm"
include "simpr2.mm"
include "simpr3.mm"
include "sylibrd.mm"
include "com23.mm"
include "imp31.mm"
include "ralrimivvva.mm"
include "df-po.mm"
include "3imtr4g.mm"

theorem isopolem
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cH: class H
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let vf: setvar f


  assert |- ( H Isom R , S ( A , B ) -> ( S Po B -> R Po A ) )

  proof
    cA
    cB
    cR
    cS
    cH
    wiso
    #
    va
    cv
    #
    @1
    cS
    wbr
    #
    wn
    #
    @1
    vb
    cv
    #
    cS
    wbr
    #
    @4
    vc
    cv
    #
    cS
    wbr
    #
    wa
    #
    @1
    @6
    cS
    wbr
    #
    wi
    #
    wa
    #
    vc
    cB
    wral
    vb
    cB
    wral
    va
    cB
    wral
    #
    vd
    cv
    #
    @13
    cR
    wbr
    #
    wn
    #
    @13
    ve
    cv
    #
    cR
    wbr
    #
    @16
    vf
    cv
    #
    cR
    wbr
    #
    wa
    #
    @13
    @18
    cR
    wbr
    #
    wi
    #
    wa
    #
    vf
    cA
    wral
    ve
    cA
    wral
    vd
    cA
    wral
    #
    cB
    cS
    wpo
    cA
    cR
    wpo
    @0
    @12
    @24
    @0
    @12
    wa
    @23
    vd
    ve
    vf
    cA
    cA
    cA
    @0
    @12
    @13
    cA
    wcel
    #
    @16
    cA
    wcel
    #
    @18
    cA
    wcel
    #
    w3a
    #
    @23
    @0
    @28
    @12
    @23
    @0
    @28
    @12
    @23
    wi
    @0
    @28
    wa
    #
    @12
    @13
    cH
    cfv
    #
    @30
    cS
    wbr
    #
    wn
    #
    @30
    @16
    cH
    cfv
    #
    cS
    wbr
    #
    @33
    @18
    cH
    cfv
    #
    cS
    wbr
    #
    wa
    #
    @30
    @35
    cS
    wbr
    #
    wi
    #
    wa
    #
    @23
    @29
    @30
    cB
    wcel
    #
    @33
    cB
    wcel
    #
    @35
    cB
    wcel
    #
    w3a
    #
    @12
    @40
    wi
    @0
    @28
    @44
    @0
    cA
    cB
    cH
    wf1o
    cA
    cB
    cH
    wf
    #
    @28
    @44
    wi
    cA
    cB
    cR
    cS
    cH
    isof1o
    cA
    cB
    cH
    f1of
    @45
    @25
    @41
    @26
    @42
    @27
    @43
    @45
    @25
    @41
    cA
    cB
    @13
    cH
    ffvelrn
    ex
    @45
    @26
    @42
    cA
    cB
    @16
    cH
    ffvelrn
    ex
    @45
    @27
    @43
    cA
    cB
    @18
    cH
    ffvelrn
    ex
    3anim123d
    3syl
    imp
    @11
    @40
    @32
    @30
    @4
    cS
    wbr
    #
    @7
    wa
    #
    @30
    @6
    cS
    wbr
    #
    wi
    #
    wa
    @32
    @34
    @33
    @6
    cS
    wbr
    #
    wa
    #
    @48
    wi
    #
    wa
    va
    vb
    vc
    @30
    @33
    @35
    cB
    cB
    cB
    @1
    @30
    wceq
    #
    @3
    @32
    @10
    @49
    @53
    @2
    @31
    @53
    @2
    @31
    wb
    @1
    @30
    @1
    @30
    cS
    breq12
    anidms
    notbid
    @53
    @8
    @47
    @9
    @48
    @53
    @5
    @46
    @7
    @1
    @30
    @4
    cS
    breq1
    anbi1d
    @1
    @30
    @6
    cS
    breq1
    imbi12d
    anbi12d
    @4
    @33
    wceq
    #
    @49
    @52
    @32
    @54
    @47
    @51
    @48
    @54
    @46
    @34
    @7
    @50
    @4
    @33
    @30
    cS
    breq2
    @4
    @33
    @6
    cS
    breq1
    anbi12d
    imbi1d
    anbi2d
    @6
    @35
    wceq
    #
    @52
    @39
    @32
    @55
    @51
    @37
    @48
    @38
    @55
    @50
    @36
    @34
    @6
    @35
    @33
    cS
    breq2
    anbi2d
    @6
    @35
    @30
    cS
    breq2
    imbi12d
    anbi2d
    rspc3v
    syl
    @29
    @15
    @32
    @22
    @39
    @29
    @14
    @31
    @29
    @0
    @25
    @25
    @14
    @31
    wb
    @0
    @28
    simpl
    #
    @0
    @25
    @26
    @27
    simpr1
    #
    @57
    cA
    cB
    @13
    @13
    cR
    cS
    cH
    isorel
    syl12anc
    notbid
    @29
    @20
    @37
    @21
    @38
    @29
    @17
    @34
    @19
    @36
    @29
    @0
    @25
    @26
    @17
    @34
    wb
    @56
    @57
    @0
    @25
    @26
    @27
    simpr2
    #
    cA
    cB
    @13
    @16
    cR
    cS
    cH
    isorel
    syl12anc
    @29
    @0
    @26
    @27
    @19
    @36
    wb
    @56
    @58
    @0
    @25
    @26
    @27
    simpr3
    #
    cA
    cB
    @16
    @18
    cR
    cS
    cH
    isorel
    syl12anc
    anbi12d
    @29
    @0
    @25
    @27
    @21
    @38
    wb
    @56
    @57
    @59
    cA
    cB
    @13
    @18
    cR
    cS
    cH
    isorel
    syl12anc
    imbi12d
    anbi12d
    sylibrd
    ex
    com23
    imp31
    ralrimivvva
    ex
    va
    vb
    vc
    cB
    cS
    df-po
    vd
    ve
    vf
    cA
    cR
    df-po
    3imtr4g
end
