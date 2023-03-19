include "cfil.mm"
include "cfv.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "cun.mm"
include "wcel.mm"
include "wral.mm"
include "w3a.mm"
include "cuni.mm"
include "wel.mm"
include "wrex.mm"
include "eluni2.mm"
include "wi.mm"
include "wa.mm"
include "ssel2.mm"
include "filelss.mm"
include "ex.mm"
include "syl.mm"
include "rexlimdva.mm"
include "3ad2ant1.mm"
include "syl5bi.mm"
include "pm4.71rd.mm"
include "cvv.mm"
include "ssn0.mm"
include "fvprc.mm"
include "necon1ai.mm"
include "3adant3.mm"
include "wsbc.mm"
include "filtop.mm"
include "a1d.mm"
include "ralimdva.mm"
include "r19.2z.mm"
include "sylan9.mm"
include "3impia.mm"
include "sylibr.mm"
include "sbcel1v.mm"
include "wn.mm"
include "0nelfil.mm"
include "ralrimiva.mm"
include "bitri.mm"
include "notbii.mm"
include "ralnex.mm"
include "bitr4i.mm"
include "simp13.mm"
include "r19.29.mm"
include "simp1.mm"
include "simpl.mm"
include "syl2an.mm"
include "simprrr.mm"
include "simpl2.mm"
include "simpl3.mm"
include "filss.mm"
include "syl13anc.mm"
include "expr.mm"
include "reximdva.mm"
include "syl3an1.mm"
include "syld.mm"
include "3imtr4g.mm"
include "cin.mm"
include "simp11.mm"
include "elun1.mm"
include "elun2.mm"
include "anim12i.mm"
include "wceq.mm"
include "eleq2.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "sylan2.mm"
include "an12s.mm"
include "ad2antlr.mm"
include "syl9r.mm"
include "impr.mm"
include "ancom2s.mm"
include "rexlimiva.mm"
include "imp.mm"
include "filin.mm"
include "3expib.mm"
include "syl2im.mm"
include "syland.mm"
include "anbi12i.mm"
include "isfild.mm"

theorem filuni
  let vf: setvar f
  let vg: setvar g
  let cF: class F
  let cX: class X
  let vh: setvar h
  let vx: setvar x
  let vy: setvar y

  disjoint f g
  disjoint F f
  disjoint F g
  disjoint X f
  disjoint X g
  disjoint f h
  disjoint f x
  disjoint f y
  disjoint g h
  disjoint g x
  disjoint g y
  disjoint h x
  disjoint h y
  disjoint F h
  disjoint x y
  disjoint F x
  disjoint F y
  disjoint X h
  disjoint X x
  disjoint X y
  assert |- ( ( F C_ ( Fil ` X ) /\ F =/= (/) /\ A. f e. F A. g e. F ( f u. g ) e. F ) -> U. F e. ( Fil ` X ) )

  proof
    cF
    cX
    cfil
    cfv
    #
    wss
    #
    cF
    c0
    wne
    #
    vf
    cv
    #
    vg
    cv
    #
    cun
    #
    cF
    wcel
    #
    vg
    cF
    wral
    #
    vf
    cF
    wral
    #
    w3a
    #
    vx
    cv
    #
    cF
    cuni
    #
    wcel
    #
    vx
    vy
    vx
    cX
    @11
    @9
    @12
    @10
    cX
    wss
    #
    @12
    vx
    vf
    wel
    #
    vf
    cF
    wrex
    #
    @9
    @13
    vf
    @10
    cF
    eluni2
    #
    @1
    @2
    @15
    @13
    wi
    @8
    @1
    @14
    @13
    vf
    cF
    @1
    @3
    cF
    wcel
    #
    wa
    #
    @3
    @0
    wcel
    #
    @14
    @13
    wi
    cF
    @0
    @3
    ssel2
    #
    @19
    @14
    @13
    @10
    @3
    cX
    filelss
    ex
    syl
    rexlimdva
    3ad2ant1
    syl5bi
    pm4.71rd
    @1
    @2
    cX
    cvv
    wcel
    #
    @8
    @1
    @2
    wa
    @0
    c0
    wne
    @21
    cF
    @0
    ssn0
    @21
    @0
    c0
    cX
    cfil
    fvprc
    necon1ai
    syl
    3adant3
    @9
    cX
    @11
    wcel
    #
    @12
    vx
    cX
    wsbc
    @9
    cX
    @3
    wcel
    #
    vf
    cF
    wrex
    #
    @22
    @1
    @2
    @8
    @24
    @1
    @8
    @23
    vf
    cF
    wral
    #
    @2
    @24
    @1
    @7
    @23
    vf
    cF
    @18
    @23
    @7
    @18
    @19
    @23
    @20
    @3
    cX
    filtop
    syl
    a1d
    ralimdva
    @2
    @25
    @24
    @23
    vf
    cF
    r19.2z
    ex
    sylan9
    3impia
    vf
    cX
    cF
    eluni2
    sylibr
    vx
    cX
    @11
    sbcel1v
    sylibr
    @9
    c0
    @3
    wcel
    #
    wn
    #
    vf
    cF
    wral
    #
    @12
    vx
    c0
    wsbc
    #
    wn
    #
    @1
    @2
    @28
    @8
    @1
    @27
    vf
    cF
    @18
    @19
    @27
    @20
    @3
    cX
    0nelfil
    syl
    ralrimiva
    3ad2ant1
    @30
    @26
    vf
    cF
    wrex
    #
    wn
    @28
    @29
    @31
    @29
    c0
    @11
    wcel
    @31
    vx
    c0
    @11
    sbcel1v
    vf
    c0
    cF
    eluni2
    bitri
    notbii
    @26
    vf
    cF
    ralnex
    bitr4i
    sylibr
    @9
    vy
    cv
    #
    cX
    wss
    #
    @10
    @32
    wss
    #
    w3a
    #
    @15
    vy
    vf
    wel
    #
    vf
    cF
    wrex
    #
    @12
    vx
    @10
    wsbc
    #
    @12
    vx
    @32
    wsbc
    #
    @35
    @15
    @7
    @14
    wa
    #
    vf
    cF
    wrex
    #
    @37
    @35
    @8
    @15
    @41
    wi
    @1
    @2
    @8
    @33
    @34
    simp13
    @8
    @15
    @41
    @7
    @14
    vf
    cF
    r19.29
    ex
    syl
    @9
    @1
    @33
    @34
    @41
    @37
    wi
    @1
    @2
    @8
    simp1
    @1
    @33
    @34
    w3a
    #
    @40
    @36
    vf
    cF
    @42
    @17
    @40
    @36
    @42
    @17
    @40
    wa
    #
    wa
    @19
    @14
    @33
    @34
    @36
    @42
    @1
    @17
    @19
    @43
    @1
    @33
    @34
    simp1
    @17
    @40
    simpl
    @20
    syl2an
    @42
    @17
    @7
    @14
    simprrr
    @1
    @33
    @34
    @43
    simpl2
    @1
    @33
    @34
    @43
    simpl3
    @10
    @32
    @3
    cX
    filss
    syl13anc
    expr
    reximdva
    syl3an1
    syld
    @38
    @12
    @15
    vx
    @10
    @11
    sbcel1v
    #
    @16
    bitri
    @39
    @32
    @11
    wcel
    @37
    vx
    @32
    @11
    sbcel1v
    vf
    @32
    cF
    eluni2
    bitri
    #
    3imtr4g
    @9
    @33
    @13
    w3a
    #
    @37
    vx
    vg
    wel
    #
    vg
    cF
    wrex
    #
    wa
    @32
    @10
    cin
    #
    vh
    cv
    #
    wcel
    #
    vh
    cF
    wrex
    #
    @39
    @38
    wa
    @12
    vx
    @49
    wsbc
    #
    @46
    @37
    @7
    @36
    wa
    #
    vf
    cF
    wrex
    #
    @48
    @52
    @46
    @8
    @37
    @55
    wi
    @1
    @2
    @8
    @33
    @13
    simp13
    @8
    @37
    @55
    @7
    @36
    vf
    cF
    r19.29
    ex
    syl
    @46
    @1
    @55
    @48
    wa
    vy
    vh
    wel
    #
    vx
    vh
    wel
    #
    wa
    #
    vh
    cF
    wrex
    #
    @52
    @1
    @2
    @8
    @33
    @13
    simp11
    @55
    @48
    @59
    @54
    @48
    @59
    wi
    #
    vf
    cF
    @17
    @36
    @7
    @60
    @17
    @36
    @7
    @60
    @7
    @48
    @6
    @47
    wa
    #
    vg
    cF
    wrex
    #
    @17
    @36
    wa
    #
    @59
    @7
    @48
    @62
    @6
    @47
    vg
    cF
    r19.29
    ex
    @63
    @61
    @59
    vg
    cF
    @36
    @61
    @59
    wi
    @17
    @4
    cF
    wcel
    @36
    @61
    @59
    @6
    @36
    @47
    @59
    @36
    @47
    wa
    @6
    @32
    @5
    wcel
    #
    @10
    @5
    wcel
    #
    wa
    #
    @59
    @36
    @64
    @47
    @65
    @32
    @3
    @4
    elun1
    @10
    @4
    @3
    elun2
    anim12i
    @58
    @66
    vh
    @5
    cF
    @50
    @5
    wceq
    @56
    @64
    @57
    @65
    @50
    @5
    @32
    eleq2
    @50
    @5
    @10
    eleq2
    anbi12d
    rspcev
    sylan2
    an12s
    ex
    ad2antlr
    rexlimdva
    syl9r
    impr
    ancom2s
    rexlimiva
    imp
    @1
    @58
    @51
    vh
    cF
    @1
    @50
    cF
    wcel
    wa
    @50
    @0
    wcel
    #
    @58
    @51
    wi
    cF
    @0
    @50
    ssel2
    @67
    @56
    @57
    @51
    @32
    @10
    @50
    cX
    filin
    3expib
    syl
    reximdva
    syl2im
    syland
    @39
    @37
    @38
    @48
    @45
    @38
    @12
    @48
    @44
    vg
    @10
    cF
    eluni2
    bitri
    anbi12i
    @53
    @49
    @11
    wcel
    @52
    vx
    @49
    @11
    sbcel1v
    vh
    @49
    cF
    eluni2
    bitri
    3imtr4g
    isfild
end
