include "cun.mm"
include "wf1o.mm"
include "cv.mm"
include "wbr.mm"
include "cfv.mm"
include "wb.mm"
include "wral.mm"
include "wiso.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "isof1o.mm"
include "syl.mm"
include "f1oun.mm"
include "syl22anc.mm"
include "wcel.mm"
include "wa.mm"
include "wo.mm"
include "wi.mm"
include "elun.mm"
include "isorel.mm"
include "sylan.mm"
include "wfn.mm"
include "f1ofn.mm"
include "adantr.mm"
include "anim1i.mm"
include "fvun1.mm"
include "syl3anc.mm"
include "adantrr.mm"
include "adantrl.mm"
include "breq12d.mm"
include "bitr4d.mm"
include "anassrs.mm"
include "3expb.mm"
include "3expia.mm"
include "ralrimiv.mm"
include "ralrimiva.mm"
include "wf.mm"
include "f1of.mm"
include "ffvelrnda.mm"
include "breq1.mm"
include "breq2.mm"
include "rspc2v.mm"
include "syl2anc.mm"
include "mpd.mm"
include "fvun2.mm"
include "3brtr4d.mm"
include "2thd.mm"
include "jaodan.mm"
include "sylan2b.mm"
include "ex.mm"
include "wn.mm"
include "notbid.mm"
include "mtbird.mm"
include "2falsed.mm"
include "df-isom.mm"
include "sylanbrc.mm"

theorem isoun
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let cS: class S
  let cG: class G
  let cH: class H
  assume isoun.1: |- ( ph -> H Isom R , S ( A , B ) )
  assume isoun.2: |- ( ph -> G Isom R , S ( C , D ) )
  assume isoun.3: |- ( ( ph /\ x e. A /\ y e. C ) -> x R y )
  assume isoun.4: |- ( ( ph /\ z e. B /\ w e. D ) -> z S w )
  assume isoun.5: |- ( ( ph /\ x e. C /\ y e. A ) -> -. x R y )
  assume isoun.6: |- ( ( ph /\ z e. D /\ w e. B ) -> -. z S w )
  assume isoun.7: |- ( ph -> ( A i^i C ) = (/) )
  assume isoun.8: |- ( ph -> ( B i^i D ) = (/) )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint B w
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint C x
  disjoint C y
  disjoint D w
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint G w
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint H w
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint R x
  disjoint R y
  disjoint S w
  disjoint S x
  disjoint S y
  disjoint S z
  disjoint ph w
  disjoint ph x
  disjoint ph y
  disjoint ph z
  assert |- ( ph -> ( H u. G ) Isom R , S ( ( A u. C ) , ( B u. D ) ) )

  proof
    wph
    cA
    cC
    cun
    #
    cB
    cD
    cun
    #
    cH
    cG
    cun
    #
    wf1o
    #
    vx
    cv
    #
    vy
    cv
    #
    cR
    wbr
    #
    @4
    @2
    cfv
    #
    @5
    @2
    cfv
    #
    cS
    wbr
    #
    wb
    #
    vy
    @0
    wral
    #
    vx
    @0
    wral
    @0
    @1
    cR
    cS
    @2
    wiso
    wph
    cA
    cB
    cH
    wf1o
    #
    cC
    cD
    cG
    wf1o
    #
    cA
    cC
    cin
    c0
    wceq
    #
    cB
    cD
    cin
    c0
    wceq
    @3
    wph
    cA
    cB
    cR
    cS
    cH
    wiso
    #
    @12
    isoun.1
    cA
    cB
    cR
    cS
    cH
    isof1o
    syl
    #
    wph
    cC
    cD
    cR
    cS
    cG
    wiso
    #
    @13
    isoun.2
    cC
    cD
    cR
    cS
    cG
    isof1o
    syl
    #
    isoun.7
    isoun.8
    cA
    cB
    cC
    cD
    cH
    cG
    f1oun
    syl22anc
    wph
    @11
    vx
    @0
    wph
    @4
    @0
    wcel
    #
    wa
    @10
    vy
    @0
    @19
    wph
    @4
    cA
    wcel
    #
    @4
    cC
    wcel
    #
    wo
    @5
    @0
    wcel
    #
    @10
    wi
    #
    @4
    cA
    cC
    elun
    wph
    @20
    @23
    @21
    wph
    @20
    wa
    #
    @22
    @10
    @22
    @24
    @5
    cA
    wcel
    #
    @5
    cC
    wcel
    #
    wo
    #
    @10
    @5
    cA
    cC
    elun
    #
    @24
    @25
    @10
    @26
    wph
    @20
    @25
    @10
    wph
    @20
    @25
    wa
    #
    wa
    #
    @6
    @4
    cH
    cfv
    #
    @5
    cH
    cfv
    #
    cS
    wbr
    #
    @9
    wph
    @15
    @29
    @6
    @33
    wb
    isoun.1
    cA
    cB
    @4
    @5
    cR
    cS
    cH
    isorel
    sylan
    @30
    @7
    @31
    @8
    @32
    cS
    wph
    @20
    @7
    @31
    wceq
    #
    @25
    @24
    cH
    cA
    wfn
    #
    cG
    cC
    wfn
    #
    @14
    @20
    wa
    @34
    wph
    @35
    @20
    wph
    @12
    @35
    @16
    cA
    cB
    cH
    f1ofn
    syl
    #
    adantr
    wph
    @36
    @20
    wph
    @13
    @36
    @18
    cC
    cD
    cG
    f1ofn
    syl
    #
    adantr
    wph
    @14
    @20
    isoun.7
    anim1i
    cA
    cC
    cH
    cG
    @4
    fvun1
    syl3anc
    #
    adantrr
    wph
    @25
    @8
    @32
    wceq
    #
    @20
    wph
    @25
    wa
    @35
    @36
    @14
    @25
    wa
    @40
    wph
    @35
    @25
    @37
    adantr
    wph
    @36
    @25
    @38
    adantr
    wph
    @14
    @25
    isoun.7
    anim1i
    cA
    cC
    cH
    cG
    @5
    fvun1
    syl3anc
    #
    adantrl
    breq12d
    bitr4d
    anassrs
    wph
    @20
    @26
    @10
    wph
    @20
    @26
    wa
    #
    wa
    #
    @6
    @9
    wph
    @20
    @26
    @6
    isoun.3
    3expb
    @43
    @31
    @5
    cG
    cfv
    #
    @7
    @8
    cS
    @43
    vz
    cv
    #
    vw
    cv
    #
    cS
    wbr
    #
    vw
    cD
    wral
    #
    vz
    cB
    wral
    #
    @31
    @44
    cS
    wbr
    #
    wph
    @49
    @42
    wph
    @48
    vz
    cB
    wph
    @45
    cB
    wcel
    #
    wa
    @47
    vw
    cD
    wph
    @51
    @46
    cD
    wcel
    @47
    isoun.4
    3expia
    ralrimiv
    ralrimiva
    adantr
    @43
    @31
    cB
    wcel
    #
    @44
    cD
    wcel
    #
    @49
    @50
    wi
    wph
    @20
    @52
    @26
    wph
    cA
    cB
    @4
    cH
    wph
    @12
    cA
    cB
    cH
    wf
    @16
    cA
    cB
    cH
    f1of
    syl
    #
    ffvelrnda
    adantrr
    wph
    @26
    @53
    @20
    wph
    cC
    cD
    @5
    cG
    wph
    @13
    cC
    cD
    cG
    wf
    @18
    cC
    cD
    cG
    f1of
    syl
    #
    ffvelrnda
    adantrl
    @47
    @50
    @31
    @46
    cS
    wbr
    vz
    vw
    @31
    @44
    cB
    cD
    @45
    @31
    @46
    cS
    breq1
    @46
    @44
    @31
    cS
    breq2
    rspc2v
    syl2anc
    mpd
    wph
    @20
    @34
    @26
    @39
    adantrr
    wph
    @26
    @8
    @44
    wceq
    #
    @20
    wph
    @26
    wa
    @35
    @36
    @14
    @26
    wa
    @56
    wph
    @35
    @26
    @37
    adantr
    wph
    @36
    @26
    @38
    adantr
    wph
    @14
    @26
    isoun.7
    anim1i
    cA
    cC
    cH
    cG
    @5
    fvun2
    syl3anc
    #
    adantrl
    3brtr4d
    2thd
    anassrs
    jaodan
    sylan2b
    ex
    wph
    @21
    wa
    #
    @22
    @10
    @22
    @58
    @27
    @10
    @28
    @58
    @25
    @10
    @26
    wph
    @21
    @25
    @10
    wph
    @21
    @25
    wa
    #
    wa
    #
    @6
    @9
    wph
    @21
    @25
    @6
    wn
    isoun.5
    3expb
    @60
    @9
    @4
    cG
    cfv
    #
    @32
    cS
    wbr
    #
    @60
    @47
    wn
    #
    vw
    cB
    wral
    #
    vz
    cD
    wral
    #
    @62
    wn
    #
    wph
    @65
    @59
    wph
    @64
    vz
    cD
    wph
    @45
    cD
    wcel
    #
    wa
    @63
    vw
    cB
    wph
    @67
    @46
    cB
    wcel
    @63
    isoun.6
    3expia
    ralrimiv
    ralrimiva
    adantr
    @60
    @61
    cD
    wcel
    #
    @32
    cB
    wcel
    #
    @65
    @66
    wi
    wph
    @21
    @68
    @25
    wph
    cC
    cD
    @4
    cG
    @55
    ffvelrnda
    adantrr
    wph
    @25
    @69
    @21
    wph
    cA
    cB
    @5
    cH
    @54
    ffvelrnda
    adantrl
    @63
    @66
    @61
    @46
    cS
    wbr
    #
    wn
    vz
    vw
    @61
    @32
    cD
    cB
    @45
    @61
    wceq
    @47
    @70
    @45
    @61
    @46
    cS
    breq1
    notbid
    @46
    @32
    wceq
    @70
    @62
    @46
    @32
    @61
    cS
    breq2
    notbid
    rspc2v
    syl2anc
    mpd
    @60
    @7
    @61
    @8
    @32
    cS
    wph
    @21
    @7
    @61
    wceq
    #
    @25
    @58
    @35
    @36
    @14
    @21
    wa
    @71
    wph
    @35
    @21
    @37
    adantr
    wph
    @36
    @21
    @38
    adantr
    wph
    @14
    @21
    isoun.7
    anim1i
    cA
    cC
    cH
    cG
    @4
    fvun2
    syl3anc
    #
    adantrr
    wph
    @25
    @40
    @21
    @41
    adantrl
    breq12d
    mtbird
    2falsed
    anassrs
    wph
    @21
    @26
    @10
    wph
    @21
    @26
    wa
    #
    wa
    #
    @6
    @61
    @44
    cS
    wbr
    #
    @9
    wph
    @17
    @73
    @6
    @75
    wb
    isoun.2
    cC
    cD
    @4
    @5
    cR
    cS
    cG
    isorel
    sylan
    @74
    @7
    @61
    @8
    @44
    cS
    wph
    @21
    @71
    @26
    @72
    adantrr
    wph
    @26
    @56
    @21
    @57
    adantrl
    breq12d
    bitr4d
    anassrs
    jaodan
    sylan2b
    ex
    jaodan
    sylan2b
    ralrimiv
    ralrimiva
    vx
    vy
    @0
    @1
    cR
    cS
    @2
    df-isom
    sylanbrc
end
