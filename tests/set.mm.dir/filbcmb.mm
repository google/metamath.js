include "cfn.mm"
include "wcel.mm"
include "c0.mm"
include "wne.mm"
include "cr.mm"
include "wss.mm"
include "w3a.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "wi.mm"
include "wral.mm"
include "wrex.mm"
include "cvv.mm"
include "reex.mm"
include "ssex.mm"
include "indexfi.mm"
include "3expia.mm"
include "sylan2.mm"
include "3adant2.mm"
include "wa.mm"
include "r19.2z.mm"
include "rexn0.mm"
include "rexlimivw.mm"
include "syl.mm"
include "ex.mm"
include "3ad2ant2.mm"
include "ad2antrr.mm"
include "sstr.mm"
include "ancoms.mm"
include "fimaxre.mm"
include "sylan.mm"
include "anasss.mm"
include "ancom2s.mm"
include "3ad2antl3.mm"
include "anassrs.mm"
include "syld.mm"
include "a1dd.mm"
include "3impd.mm"
include "nfv.mm"
include "nfcv.mm"
include "nfre1.mm"
include "nfral.mm"
include "nfan.mm"
include "nfra1.mm"
include "nfrex.mm"
include "weq.mm"
include "breq1.mm"
include "imbi1d.mm"
include "ralbidv.mm"
include "cbvrexv.mm"
include "rsp.mm"
include "ssel2.mm"
include "adantlr.mm"
include "adantrr.mm"
include "ad2ant2r.mm"
include "adantr.mm"
include "rspccva.mm"
include "adantll.mm"
include "simplrr.mm"
include "letrd.mm"
include "pm2.27.mm"
include "ad2antlr.mm"
include "mpid.mm"
include "syl5.mm"
include "rexlimdva.mm"
include "syl5bi.mm"
include "ralimdva.mm"
include "imp.mm"
include "an32s.mm"
include "exp32.mm"
include "ralrimi.mm"
include "reximdai.mm"
include "ssrexv.mm"
include "exp43.mm"
include "3ad2ant3.mm"
include "mpdd.mm"

theorem filbcmb
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let vu: setvar u
  let vv: setvar v
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
  disjoint ph y
  disjoint A u
  disjoint A v
  disjoint A w
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint B u
  disjoint B v
  disjoint B w
  disjoint ph u
  disjoint ph v
  disjoint ph w
  assert |- ( ( A e. Fin /\ A =/= (/) /\ B C_ RR ) -> ( A. x e. A E. y e. B A. z e. B ( y <_ z -> ph ) -> E. y e. B A. z e. B ( y <_ z -> A. x e. A ph ) ) )

  proof
    cA
    cfn
    wcel
    #
    cA
    c0
    wne
    #
    cB
    cr
    wss
    #
    w3a
    #
    vy
    cv
    #
    vz
    cv
    #
    cle
    wbr
    #
    wph
    wi
    #
    vz
    cB
    wral
    #
    vy
    cB
    wrex
    vx
    cA
    wral
    #
    vw
    cv
    #
    cB
    wss
    #
    @8
    vy
    @10
    wrex
    #
    vx
    cA
    wral
    #
    @8
    vx
    cA
    wrex
    vy
    @10
    wral
    #
    w3a
    #
    vw
    cfn
    wrex
    #
    @6
    wph
    vx
    cA
    wral
    #
    wi
    #
    vz
    cB
    wral
    #
    vy
    cB
    wrex
    #
    @0
    @2
    @9
    @16
    wi
    #
    @1
    @2
    @0
    cB
    cvv
    wcel
    #
    @21
    cB
    cr
    reex
    ssex
    @0
    @22
    @9
    @16
    @8
    vx
    vy
    cA
    cB
    cvv
    vw
    indexfi
    3expia
    sylan2
    3adant2
    @3
    @15
    @20
    vw
    cfn
    @3
    @10
    cfn
    wcel
    #
    wa
    #
    @15
    vu
    cv
    #
    @4
    cle
    wbr
    #
    vu
    @10
    wral
    #
    vy
    @10
    wrex
    #
    @20
    @24
    @11
    @13
    @14
    @28
    @24
    @11
    @13
    @14
    @28
    wi
    wi
    @24
    @11
    wa
    #
    @13
    @28
    @14
    @29
    @13
    @10
    c0
    wne
    #
    @28
    @3
    @13
    @30
    wi
    #
    @23
    @11
    @1
    @0
    @31
    @2
    @1
    @13
    @30
    @1
    @13
    wa
    @12
    vx
    cA
    wrex
    @30
    @12
    vx
    cA
    r19.2z
    @12
    @30
    vx
    cA
    @8
    vy
    @10
    rexn0
    rexlimivw
    syl
    ex
    3ad2ant2
    ad2antrr
    @3
    @23
    @11
    @30
    @28
    wi
    #
    @2
    @0
    @23
    @11
    wa
    @32
    @1
    @2
    @11
    @23
    @32
    @2
    @11
    @23
    @32
    @2
    @11
    wa
    #
    @10
    cr
    wss
    #
    @23
    @32
    @11
    @2
    @34
    @10
    cB
    cr
    sstr
    ancoms
    @34
    @23
    @30
    @28
    vy
    vu
    @10
    fimaxre
    3expia
    sylan
    anasss
    ancom2s
    3ad2antl3
    anassrs
    syld
    a1dd
    ex
    3impd
    @3
    @15
    @28
    @20
    wi
    #
    wi
    #
    @23
    @2
    @0
    @36
    @1
    @2
    @11
    @13
    @14
    @35
    @2
    @11
    @13
    @14
    @35
    @33
    @13
    @14
    wa
    #
    wa
    @28
    @19
    vy
    @10
    wrex
    #
    @20
    @33
    @13
    @28
    @38
    wi
    @14
    @33
    @13
    wa
    #
    @27
    @19
    vy
    @10
    @33
    @13
    vy
    @33
    vy
    nfv
    @12
    vy
    vx
    cA
    vy
    cA
    nfcv
    @8
    vy
    @10
    nfre1
    nfral
    nfan
    @39
    @4
    @10
    wcel
    #
    @27
    @19
    @39
    @40
    @27
    wa
    #
    wa
    @18
    vz
    cB
    @39
    @41
    vz
    @33
    @13
    vz
    @33
    vz
    nfv
    @12
    vz
    vx
    cA
    vz
    cA
    nfcv
    @8
    vz
    vy
    @10
    vz
    @10
    nfcv
    @7
    vz
    cB
    nfra1
    nfrex
    nfral
    nfan
    @41
    vz
    nfv
    nfan
    @33
    @41
    @13
    @5
    cB
    wcel
    #
    @18
    wi
    @33
    @41
    wa
    #
    @13
    wa
    @42
    @6
    @17
    @43
    @42
    @6
    wa
    #
    @13
    @17
    @43
    @44
    wa
    #
    @13
    @17
    @45
    @12
    wph
    vx
    cA
    @12
    vv
    cv
    #
    @5
    cle
    wbr
    #
    wph
    wi
    #
    vz
    cB
    wral
    #
    vv
    @10
    wrex
    @45
    vx
    cv
    cA
    wcel
    #
    wa
    #
    wph
    @8
    @49
    vy
    vv
    @10
    vy
    vv
    weq
    #
    @7
    @48
    vz
    cB
    @52
    @6
    @47
    wph
    @4
    @46
    @5
    cle
    breq1
    imbi1d
    ralbidv
    cbvrexv
    @51
    @49
    wph
    vv
    @10
    @45
    @46
    @10
    wcel
    #
    @49
    wph
    wi
    @50
    @49
    @42
    @48
    wi
    #
    @45
    @53
    wa
    #
    wph
    @48
    vz
    cB
    rsp
    @55
    @54
    @47
    wph
    @55
    @46
    @4
    @5
    @43
    @53
    @46
    cr
    wcel
    #
    @44
    @33
    @53
    @56
    @41
    @2
    @11
    @53
    @56
    @11
    @53
    wa
    @2
    @46
    cB
    wcel
    @56
    @10
    cB
    @46
    ssel2
    cB
    cr
    @46
    ssel2
    sylan2
    anassrs
    adantlr
    adantlr
    @43
    @4
    cr
    wcel
    #
    @44
    @53
    @33
    @40
    @57
    @27
    @2
    @11
    @40
    @57
    @11
    @40
    wa
    @2
    @4
    cB
    wcel
    @57
    @10
    cB
    @4
    ssel2
    cB
    cr
    @4
    ssel2
    sylan2
    anassrs
    adantrr
    ad2antrr
    @45
    @5
    cr
    wcel
    #
    @53
    @33
    @42
    @58
    @41
    @6
    @2
    @42
    @58
    @11
    cB
    cr
    @5
    ssel2
    adantlr
    ad2ant2r
    adantr
    @43
    @53
    @46
    @4
    cle
    wbr
    #
    @44
    @41
    @53
    @59
    @33
    @27
    @53
    @59
    @40
    @26
    @59
    vu
    @46
    @10
    @25
    @46
    @4
    cle
    breq1
    rspccva
    adantll
    adantll
    adantlr
    @43
    @42
    @6
    @53
    simplrr
    letrd
    @44
    @54
    @48
    wi
    #
    @43
    @53
    @42
    @60
    @6
    @42
    @48
    pm2.27
    adantr
    ad2antlr
    mpid
    syl5
    adantlr
    rexlimdva
    syl5bi
    ralimdva
    imp
    an32s
    exp32
    an32s
    ralrimi
    exp32
    reximdai
    adantrr
    @11
    @38
    @20
    wi
    @2
    @37
    @19
    vy
    @10
    cB
    ssrexv
    ad2antlr
    syld
    exp43
    3impd
    3ad2ant3
    adantr
    mpdd
    rexlimdva
    syld
end
