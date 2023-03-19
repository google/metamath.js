include "cz.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "clt.mm"
include "wn.mm"
include "wi.mm"
include "wa.mm"
include "wceq.mm"
include "breq1.mm"
include "cbvralv.mm"
include "breq2.mm"
include "ralbidv.mm"
include "syl5bb.mm"
include "cbvrexv.mm"
include "wcel.mm"
include "cneg.mm"
include "crab.mm"
include "cr.mm"
include "cinf.mm"
include "cuz.mm"
include "cfv.mm"
include "w3a.mm"
include "simp1rl.mm"
include "znegcld.mm"
include "simp2.mm"
include "zred.mm"
include "simp3.mm"
include "simp1rr.mm"
include "rspcv.mm"
include "sylc.mm"
include "lenegcon1d.mm"
include "eluz2.mm"
include "syl3anbrc.mm"
include "rabssdv.mm"
include "wex.mm"
include "n0.mm"
include "ssel2.mm"
include "zcnd.mm"
include "negnegd.mm"
include "simpr.mm"
include "eqeltrd.mm"
include "negeq.mm"
include "eleq1d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "ex.mm"
include "exlimdv.mm"
include "imp.mm"
include "sylan2b.mm"
include "adantr.mm"
include "rabn0.mm"
include "sylibr.mm"
include "infssuzcl.mm"
include "cbvrabv.mm"
include "elrab2.mm"
include "simprbi.mm"
include "syl.mm"
include "ssrab2.mm"
include "sseldi.mm"
include "simpll.mm"
include "sselda.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "infssuzle.mm"
include "lenegcon2d.mm"
include "lenltd.mm"
include "mpbid.mm"
include "ralrimiva.mm"
include "ralrimivw.mm"
include "notbid.mm"
include "imbi1d.mm"
include "anbi12d.mm"
include "syl12anc.mm"
include "rexlimdvaa.mm"
include "syl5bi.mm"
include "3impia.mm"

theorem zsupss
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let vm: setvar m
  let vn: setvar n
  let vw: setvar w
  let cM: class M
  let cZ: class Z

  disjoint x y
  disjoint x z
  disjoint A x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint m n
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint A m
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint A n
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint A w
  disjoint B n
  disjoint M x
  disjoint M y
  disjoint Z x
  assert |- ( ( A C_ ZZ /\ A =/= (/) /\ E. x e. ZZ A. y e. A y <_ x ) -> E. x e. A ( A. y e. A -. x < y /\ A. y e. B ( y < x -> E. z e. A y < z ) ) )

  proof
    cA
    cz
    wss
    #
    cA
    c0
    wne
    #
    vy
    cv
    #
    vx
    cv
    #
    cle
    wbr
    #
    vy
    cA
    wral
    #
    vx
    cz
    wrex
    #
    @3
    @2
    clt
    wbr
    #
    wn
    #
    vy
    cA
    wral
    #
    @2
    @3
    clt
    wbr
    #
    @2
    vz
    cv
    #
    clt
    wbr
    #
    vz
    cA
    wrex
    #
    wi
    #
    vy
    cB
    wral
    #
    wa
    #
    vx
    cA
    wrex
    #
    @6
    vm
    cv
    #
    vn
    cv
    #
    cle
    wbr
    #
    vm
    cA
    wral
    #
    vn
    cz
    wrex
    @0
    @1
    wa
    #
    @17
    @5
    @21
    vx
    vn
    cz
    @5
    @18
    @3
    cle
    wbr
    #
    vm
    cA
    wral
    @3
    @19
    wceq
    #
    @21
    @4
    @23
    vy
    vm
    cA
    @2
    @18
    @3
    cle
    breq1
    cbvralv
    @24
    @23
    @20
    vm
    cA
    @3
    @19
    @18
    cle
    breq2
    ralbidv
    syl5bb
    cbvrexv
    @22
    @21
    @17
    vn
    cz
    @22
    @19
    cz
    wcel
    #
    @21
    wa
    #
    wa
    #
    vw
    cv
    #
    cneg
    #
    cA
    wcel
    #
    vw
    cz
    crab
    #
    cr
    clt
    cinf
    #
    cneg
    #
    cA
    wcel
    #
    @33
    @2
    clt
    wbr
    #
    wn
    #
    vy
    cA
    wral
    #
    @2
    @33
    clt
    wbr
    #
    @13
    wi
    #
    vy
    cB
    wral
    #
    @17
    @27
    @32
    @31
    wcel
    #
    @34
    @27
    @31
    @19
    cneg
    #
    cuz
    cfv
    #
    wss
    #
    @31
    c0
    wne
    #
    @41
    @27
    @30
    vw
    cz
    @43
    @27
    @28
    cz
    wcel
    #
    @30
    w3a
    #
    @42
    cz
    wcel
    #
    @46
    @42
    @28
    cle
    wbr
    @28
    @43
    wcel
    @47
    @19
    @25
    @21
    @22
    @46
    @30
    simp1rl
    #
    znegcld
    @27
    @46
    @30
    simp2
    #
    @47
    @28
    @19
    @47
    @28
    @50
    zred
    @47
    @19
    @49
    zred
    @47
    @30
    @21
    @29
    @19
    cle
    wbr
    #
    @27
    @46
    @30
    simp3
    @25
    @21
    @22
    @46
    @30
    simp1rr
    @20
    @51
    vm
    @29
    cA
    @18
    @29
    @19
    cle
    breq1
    rspcv
    sylc
    lenegcon1d
    @42
    @28
    eluz2
    syl3anbrc
    rabssdv
    #
    @27
    @30
    vw
    cz
    wrex
    #
    @45
    @22
    @53
    @26
    @1
    @0
    @19
    cA
    wcel
    #
    vn
    wex
    #
    @53
    vn
    cA
    n0
    @0
    @55
    @53
    @0
    @54
    @53
    vn
    @0
    @54
    @53
    @0
    @54
    wa
    #
    @48
    @42
    cneg
    #
    cA
    wcel
    #
    @53
    @56
    @19
    cA
    cz
    @19
    ssel2
    #
    znegcld
    @56
    @57
    @19
    cA
    @56
    @19
    @56
    @19
    @59
    zcnd
    negnegd
    @0
    @54
    simpr
    eqeltrd
    @30
    @58
    vw
    @42
    cz
    @28
    @42
    wceq
    @29
    @57
    cA
    @28
    @42
    negeq
    eleq1d
    rspcev
    syl2anc
    ex
    exlimdv
    imp
    sylan2b
    adantr
    @30
    vw
    cz
    rabn0
    sylibr
    @31
    @42
    infssuzcl
    syl2anc
    #
    @41
    @32
    cz
    wcel
    @34
    @42
    cA
    wcel
    #
    @34
    vn
    @32
    cz
    @31
    @19
    @32
    wceq
    @42
    @33
    cA
    @19
    @32
    negeq
    eleq1d
    @30
    @61
    vw
    vn
    cz
    @28
    @19
    wceq
    @29
    @42
    cA
    @28
    @19
    negeq
    eleq1d
    cbvrabv
    elrab2
    simprbi
    syl
    #
    @27
    @36
    vy
    cA
    @27
    @2
    cA
    wcel
    #
    wa
    #
    @2
    @33
    cle
    wbr
    @36
    @64
    @32
    @2
    @64
    @32
    @64
    @31
    cz
    @32
    @30
    vw
    cz
    ssrab2
    @27
    @41
    @63
    @60
    adantr
    sseldi
    #
    zred
    @64
    @2
    @27
    cA
    cz
    @2
    @0
    @1
    @26
    simpll
    sselda
    #
    zred
    #
    @64
    @44
    @2
    cneg
    #
    @31
    wcel
    #
    @32
    @68
    cle
    wbr
    @27
    @44
    @63
    @52
    adantr
    @64
    @68
    cz
    wcel
    @68
    cneg
    #
    cA
    wcel
    #
    @69
    @64
    @2
    @66
    znegcld
    @64
    @70
    @2
    cA
    @64
    @2
    @64
    @2
    @66
    zcnd
    negnegd
    @27
    @63
    simpr
    eqeltrd
    @30
    @71
    vw
    @68
    cz
    @28
    @68
    wceq
    @29
    @70
    cA
    @28
    @68
    negeq
    eleq1d
    elrab
    sylanbrc
    @68
    @31
    @42
    infssuzle
    syl2anc
    lenegcon2d
    @64
    @2
    @33
    @67
    @64
    @33
    @64
    @32
    @65
    znegcld
    zred
    lenltd
    mpbid
    ralrimiva
    @27
    @39
    vy
    cB
    @27
    @34
    @39
    @62
    @34
    @38
    @13
    @12
    @38
    vz
    @33
    cA
    @11
    @33
    @2
    clt
    breq2
    rspcev
    ex
    syl
    ralrimivw
    @16
    @37
    @40
    wa
    vx
    @33
    cA
    @3
    @33
    wceq
    #
    @9
    @37
    @15
    @40
    @72
    @8
    @36
    vy
    cA
    @72
    @7
    @35
    @3
    @33
    @2
    clt
    breq1
    notbid
    ralbidv
    @72
    @14
    @39
    vy
    cB
    @72
    @10
    @38
    @13
    @3
    @33
    @2
    clt
    breq2
    imbi1d
    ralbidv
    anbi12d
    rspcev
    syl12anc
    rexlimdvaa
    syl5bi
    3impia
end
