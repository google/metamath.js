include "cr.mm"
include "wss.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "wral.mm"
include "cle.mm"
include "wa.mm"
include "wrex.mm"
include "wi.mm"
include "c0.mm"
include "wne.mm"
include "w3a.mm"
include "wn.mm"
include "wcel.mm"
include "nfv.mm"
include "nfra1.mm"
include "nf3an.mm"
include "nfan.mm"
include "nfra2.mm"
include "simprrl.mm"
include "r19.21bi.mm"
include "simpl2l.mm"
include "sselda.mm"
include "simplrl.mm"
include "lenltd.mm"
include "mpbird.mm"
include "ex.mm"
include "simpl3.mm"
include "simp2.mm"
include "simpr.mm"
include "rsp.mm"
include "com12.mm"
include "adantl.mm"
include "ssel2.mm"
include "adantlr.mm"
include "adantr.mm"
include "simplr.mm"
include "ltnsym.mm"
include "syl2anc.mm"
include "syld.mm"
include "an32s.mm"
include "ralimdva.mm"
include "syl2an.mm"
include "mpd.mm"
include "wceq.mm"
include "breq2.mm"
include "notbid.mm"
include "cbvralv.mm"
include "sylib.mm"
include "ralnex.mm"
include "simp2r.mm"
include "simplrr.mm"
include "breq1.mm"
include "rexbidv.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "sylc.mm"
include "mtod.mm"
include "simprll.mm"
include "expr.mm"
include "anim12d.mm"
include "expd.mm"
include "ralrimd.mm"
include "ralrimi.mm"
include "simp2l.mm"
include "simp1l.mm"
include "wex.mm"
include "simp1r.mm"
include "n0.mm"
include "sseld.mm"
include "ralcom.mm"
include "ralbidv.mm"
include "rspccv.mm"
include "sylbi.mm"
include "3ad2ant3.mm"
include "jcad.mm"
include "eximdv.mm"
include "df-rex.mm"
include "sylibr.mm"
include "axsup.mm"
include "syl3anc.mm"
include "reximddv.mm"
include "3expib.mm"
include "c1.mm"
include "1re.mm"
include "rzal.mm"
include "anbi12d.mm"
include "2ralbidv.mm"
include "rspcev.mm"
include "sylancr.mm"
include "a1d.mm"
include "ralrimivw.mm"
include "pm2.61iine.mm"
include "3impa.mm"

theorem dedekind
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let vw: setvar w

  disjoint A x
  disjoint A y
  disjoint A z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint A w
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint B w
  assert |- ( ( A C_ RR /\ B C_ RR /\ A. x e. A A. y e. B x < y ) -> E. z e. RR A. x e. A A. y e. B ( x <_ z /\ z <_ y ) )

  proof
    cA
    cr
    wss
    #
    cB
    cr
    wss
    #
    vx
    cv
    #
    vy
    cv
    #
    clt
    wbr
    #
    vy
    cB
    wral
    #
    vx
    cA
    wral
    #
    @2
    vz
    cv
    #
    cle
    wbr
    #
    @7
    @3
    cle
    wbr
    #
    wa
    #
    vy
    cB
    wral
    #
    vx
    cA
    wral
    #
    vz
    cr
    wrex
    #
    @0
    @1
    wa
    #
    @6
    wa
    #
    @13
    wi
    cA
    cB
    c0
    c0
    cA
    c0
    wne
    #
    cB
    c0
    wne
    #
    wa
    #
    @14
    @6
    @13
    @18
    @14
    @6
    w3a
    #
    @7
    @2
    clt
    wbr
    wn
    #
    vx
    cA
    wral
    #
    @2
    @7
    clt
    wbr
    #
    @2
    vw
    cv
    #
    clt
    wbr
    #
    vw
    cA
    wrex
    #
    wi
    #
    vx
    cr
    wral
    #
    wa
    #
    @12
    vz
    cr
    @19
    @7
    cr
    wcel
    #
    @28
    wa
    #
    wa
    #
    @11
    vx
    cA
    @19
    @30
    vx
    @18
    @14
    @6
    vx
    @18
    vx
    nfv
    @14
    vx
    nfv
    @5
    vx
    cA
    nfra1
    nf3an
    @29
    @28
    vx
    @29
    vx
    nfv
    @21
    @27
    vx
    @20
    vx
    cA
    nfra1
    @26
    vx
    cr
    nfra1
    nfan
    nfan
    nfan
    @31
    @2
    cA
    wcel
    #
    @10
    vy
    cB
    @19
    @30
    vy
    @18
    @14
    @6
    vy
    @18
    vy
    nfv
    @14
    vy
    nfv
    @4
    vx
    vy
    cA
    cB
    nfra2
    nf3an
    @30
    vy
    nfv
    nfan
    @32
    vy
    nfv
    @31
    @32
    @3
    cB
    wcel
    #
    @10
    @31
    @32
    @8
    @33
    @9
    @31
    @32
    @8
    @31
    @32
    wa
    #
    @8
    @20
    @31
    @20
    vx
    cA
    @19
    @29
    @21
    @27
    simprrl
    r19.21bi
    @34
    @2
    @7
    @31
    cA
    cr
    @2
    @0
    @1
    @18
    @6
    @30
    simpl2l
    sselda
    @19
    @29
    @28
    @32
    simplrl
    lenltd
    mpbird
    ex
    @19
    @30
    @33
    @9
    @19
    @30
    @33
    wa
    #
    wa
    #
    @9
    @3
    @7
    clt
    wbr
    #
    wn
    @36
    @37
    @3
    @23
    clt
    wbr
    #
    vw
    cA
    wrex
    #
    @36
    @38
    wn
    #
    vw
    cA
    wral
    #
    @39
    wn
    @36
    @3
    @2
    clt
    wbr
    #
    wn
    #
    vx
    cA
    wral
    #
    @41
    @36
    @6
    @44
    @18
    @14
    @6
    @35
    simpl3
    @19
    @14
    @33
    @6
    @44
    wi
    @35
    @18
    @14
    @6
    simp2
    @30
    @33
    simpr
    #
    @14
    @33
    wa
    @5
    @43
    vx
    cA
    @14
    @32
    @33
    @5
    @43
    wi
    @14
    @32
    wa
    #
    @33
    wa
    #
    @5
    @4
    @43
    @33
    @5
    @4
    wi
    @46
    @5
    @33
    @4
    @4
    vy
    cB
    rsp
    com12
    adantl
    @47
    @2
    cr
    wcel
    #
    @3
    cr
    wcel
    #
    @4
    @43
    wi
    @46
    @48
    @33
    @0
    @32
    @48
    @1
    cA
    cr
    @2
    ssel2
    adantlr
    adantr
    @46
    cB
    cr
    @3
    @0
    @1
    @32
    simplr
    sselda
    @2
    @3
    ltnsym
    syl2anc
    syld
    an32s
    ralimdva
    syl2an
    mpd
    @43
    @40
    vx
    vw
    cA
    @2
    @23
    wceq
    @42
    @38
    @2
    @23
    @3
    clt
    breq2
    notbid
    cbvralv
    sylib
    @38
    vw
    cA
    ralnex
    sylib
    @36
    @49
    @27
    @37
    @39
    wi
    #
    @19
    @1
    @33
    @49
    @35
    @18
    @0
    @1
    @6
    simp2r
    #
    @45
    cB
    cr
    @3
    ssel2
    syl2an
    #
    @35
    @27
    @19
    @29
    @21
    @27
    @33
    simplrr
    adantl
    @26
    @50
    vx
    @3
    cr
    @2
    @3
    wceq
    #
    @22
    @37
    @25
    @39
    @2
    @3
    @7
    clt
    breq1
    @53
    @24
    @38
    vw
    cA
    @2
    @3
    @23
    clt
    breq1
    rexbidv
    imbi12d
    rspcv
    sylc
    mtod
    @36
    @7
    @3
    @19
    @29
    @28
    @33
    simprll
    @52
    lenltd
    mpbird
    expr
    anim12d
    expd
    ralrimd
    ralrimi
    @19
    @0
    @16
    @22
    vx
    cA
    wral
    #
    vz
    cr
    wrex
    #
    @28
    vz
    cr
    wrex
    @18
    @0
    @1
    @6
    simp2l
    @16
    @17
    @14
    @6
    simp1l
    @19
    @29
    @54
    wa
    #
    vz
    wex
    #
    @55
    @19
    @7
    cB
    wcel
    #
    vz
    wex
    #
    @57
    @19
    @17
    @59
    @16
    @17
    @14
    @6
    simp1r
    vz
    cB
    n0
    sylib
    @19
    @58
    @56
    vz
    @19
    @58
    @29
    @54
    @19
    cB
    cr
    @7
    @51
    sseld
    @6
    @18
    @58
    @54
    wi
    #
    @14
    @6
    @4
    vx
    cA
    wral
    #
    vy
    cB
    wral
    @60
    @4
    vx
    vy
    cA
    cB
    ralcom
    @61
    @54
    vy
    @7
    cB
    @3
    @7
    wceq
    @4
    @22
    vx
    cA
    @3
    @7
    @2
    clt
    breq2
    ralbidv
    rspccv
    sylbi
    3ad2ant3
    jcad
    eximdv
    mpd
    @54
    vz
    cr
    df-rex
    sylibr
    vz
    vx
    vw
    cA
    axsup
    syl3anc
    reximddv
    3expib
    cA
    c0
    wceq
    #
    @13
    @15
    @62
    c1
    cr
    wcel
    #
    @2
    c1
    cle
    wbr
    #
    c1
    @3
    cle
    wbr
    #
    wa
    #
    vy
    cB
    wral
    #
    vx
    cA
    wral
    #
    @13
    1re
    @67
    vx
    cA
    rzal
    @12
    @68
    vz
    c1
    cr
    @7
    c1
    wceq
    #
    @10
    @66
    vx
    vy
    cA
    cB
    @69
    @8
    @64
    @9
    @65
    @7
    c1
    @2
    cle
    breq2
    @7
    c1
    @3
    cle
    breq1
    anbi12d
    2ralbidv
    rspcev
    #
    sylancr
    a1d
    cB
    c0
    wceq
    #
    @13
    @15
    @71
    @63
    @68
    @13
    1re
    @71
    @67
    vx
    cA
    @66
    vy
    cB
    rzal
    ralrimivw
    @70
    sylancr
    a1d
    pm2.61iine
    3impa
end
