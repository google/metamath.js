include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "ciun.mm"
include "wss.mm"
include "cv.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "cdif.mm"
include "w3a.mm"
include "cun.mm"
include "wn.mm"
include "wi.mm"
include "wral.mm"
include "crest.mm"
include "co.mm"
include "cconn.mm"
include "ex.mm"
include "ralrimiv.mm"
include "iunss.mm"
include "biimpri.mm"
include "syl.mm"
include "wa.mm"
include "wo.mm"
include "biimpi.mm"
include "simprd.mm"
include "wrex.mm"
include "wex.mm"
include "simp-4r.mm"
include "n0.mm"
include "inss2.mm"
include "id.mm"
include "sseldi.mm"
include "eliun.mm"
include "rexn0.mm"
include "exlimiv.mm"
include "wnf.mm"
include "nfv.mm"
include "nfan.mm"
include "nfcv.mm"
include "nfiu1.mm"
include "nfin.mm"
include "nfne.mm"
include "nfdif.mm"
include "nfss.mm"
include "nfbii.mm"
include "mpbir.mm"
include "simp-6l.mm"
include "sylan.mm"
include "ralrimi.mm"
include "r19.2z.mm"
include "ancoms.mm"
include "syl2anc.mm"
include "sseldd.mm"
include "elun.mm"
include "sylbir.mm"
include "simp-6r.mm"
include "simp-5r.mm"
include "simpllr.mm"
include "simplr.mm"
include "iunconnlem.mm"
include "incom.mm"
include "syl5eqss.mm"
include "uncom.mm"
include "syl6sseqr.mm"
include "pm4.56.mm"
include "idiALT.mm"
include "pm2.65da.mm"
include "ex3.mm"
include "3impd.mm"
include "3expia.mm"
include "impd.mm"
include "ralrimivv.mm"
include "connsub.mm"
include "biimp3ar.mm"
include "syl3anc.mm"

theorem iunconnlem2
  let wph: wff ph
  let wps: wff ps
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cP: class P
  let vk: setvar k
  let cJ: class J
  let cX: class X
  let vw: setvar w
  assume iunconnlem2.1: |- ( ps <-> ( ( ( ( ( ( ph /\ u e. J ) /\ v e. J ) /\ ( u i^i U_ k e. A B ) =/= (/) ) /\ ( v i^i U_ k e. A B ) =/= (/) ) /\ ( u i^i v ) C_ ( X \ U_ k e. A B ) ) /\ U_ k e. A B C_ ( u u. v ) ) )
  assume iunconnlem2.2: |- ( ph -> J e. ( TopOn ` X ) )
  assume iunconnlem2.3: |- ( ( ph /\ k e. A ) -> B C_ X )
  assume iunconnlem2.4: |- ( ( ph /\ k e. A ) -> P e. B )
  assume iunconnlem2.5: |- ( ( ph /\ k e. A ) -> ( J |`t B ) e. Conn )

  disjoint k u
  disjoint k v
  disjoint k ph
  disjoint u v
  disjoint ph u
  disjoint ph v
  disjoint A k
  disjoint A u
  disjoint A v
  disjoint B u
  disjoint B v
  disjoint J k
  disjoint J u
  disjoint J v
  disjoint P k
  disjoint X k
  disjoint X u
  disjoint X v
  disjoint k w
  disjoint u w
  disjoint A w
  disjoint B w
  assert |- ( ph -> ( J |`t U_ k e. A B ) e. Conn )

  proof
    wph
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    vk
    cA
    cB
    ciun
    #
    cX
    wss
    #
    vu
    cv
    #
    @1
    cin
    #
    c0
    wne
    #
    vv
    cv
    #
    @1
    cin
    #
    c0
    wne
    #
    @3
    @6
    cin
    #
    cX
    @1
    cdif
    #
    wss
    #
    w3a
    @1
    @3
    @6
    cun
    #
    wss
    #
    wn
    #
    wi
    #
    vv
    cJ
    wral
    vu
    cJ
    wral
    #
    cJ
    @1
    crest
    co
    cconn
    wcel
    #
    iunconnlem2.2
    wph
    cB
    cX
    wss
    #
    vk
    cA
    wral
    #
    @2
    wph
    @18
    vk
    cA
    wph
    vk
    cv
    cA
    wcel
    #
    @18
    iunconnlem2.3
    ex
    ralrimiv
    @2
    @19
    vk
    cA
    cB
    cX
    iunss
    biimpri
    syl
    wph
    @15
    vu
    vv
    cJ
    cJ
    wph
    @3
    cJ
    wcel
    #
    @6
    cJ
    wcel
    #
    @15
    wph
    @21
    @22
    @15
    wi
    wph
    @21
    @22
    @15
    wph
    @21
    @22
    w3a
    @5
    @8
    @11
    @14
    wph
    @21
    @22
    @5
    @8
    @11
    @14
    wi
    #
    wi
    wph
    @21
    wa
    #
    @22
    wa
    #
    @5
    wa
    #
    @8
    @23
    @26
    @8
    wa
    #
    @11
    @14
    @27
    @11
    wa
    #
    @13
    cP
    @3
    wcel
    #
    cP
    @6
    wcel
    #
    wo
    #
    @28
    @13
    wa
    #
    wps
    @31
    iunconnlem2.1
    wps
    cP
    @12
    wcel
    #
    @31
    wps
    @1
    @12
    cP
    wps
    @28
    @13
    wps
    @32
    iunconnlem2.1
    biimpi
    #
    simprd
    #
    wps
    cP
    cB
    wcel
    #
    vk
    cA
    wrex
    #
    cP
    @1
    wcel
    #
    wps
    cA
    c0
    wne
    #
    @36
    vk
    cA
    wral
    #
    @37
    wps
    vw
    cv
    #
    @4
    wcel
    #
    vw
    wex
    #
    @39
    wps
    @5
    @43
    wps
    @32
    @5
    @34
    @25
    @5
    @8
    @11
    @13
    simp-4r
    syl
    #
    @5
    @43
    vw
    @4
    n0
    biimpi
    syl
    @42
    @39
    vw
    @42
    @41
    cB
    wcel
    #
    vk
    cA
    wrex
    #
    @39
    @42
    @41
    @1
    wcel
    #
    @46
    @42
    @4
    @1
    @41
    @3
    @1
    inss2
    @42
    id
    sseldi
    @47
    @46
    vk
    @41
    cA
    cB
    eliun
    biimpi
    syl
    @45
    vk
    cA
    rexn0
    syl
    exlimiv
    syl
    wps
    @36
    vk
    cA
    wps
    vk
    wnf
    @32
    vk
    wnf
    @28
    @13
    vk
    @27
    @11
    vk
    @26
    @8
    vk
    @25
    @5
    vk
    @24
    @22
    vk
    @24
    vk
    nfv
    @22
    vk
    nfv
    nfan
    vk
    @4
    c0
    vk
    @3
    @1
    vk
    @3
    nfcv
    vk
    cA
    cB
    nfiu1
    #
    nfin
    vk
    c0
    nfcv
    #
    nfne
    nfan
    vk
    @7
    c0
    vk
    @6
    @1
    vk
    @6
    nfcv
    @48
    nfin
    @49
    nfne
    nfan
    vk
    @9
    @10
    vk
    @9
    nfcv
    vk
    cX
    @1
    vk
    cX
    nfcv
    @48
    nfdif
    nfss
    nfan
    vk
    @1
    @12
    @48
    vk
    @12
    nfcv
    nfss
    nfan
    wps
    @32
    vk
    iunconnlem2.1
    nfbii
    mpbir
    #
    wps
    @20
    @36
    wps
    wph
    @20
    @36
    wps
    @32
    wph
    @34
    wph
    @21
    @22
    @5
    @8
    @11
    @13
    simp-6l
    syl
    #
    iunconnlem2.4
    sylan
    #
    ex
    ralrimi
    @40
    @39
    @37
    @39
    @40
    @37
    @36
    vk
    cA
    r19.2z
    ancoms
    ancoms
    syl2anc
    @38
    @37
    vk
    cP
    cA
    cB
    eliun
    biimpri
    syl
    sseldd
    @33
    @31
    cP
    @3
    @6
    elun
    biimpi
    syl
    sylbir
    @32
    wps
    @31
    wn
    #
    iunconnlem2.1
    wps
    @29
    wn
    #
    @30
    wn
    #
    @53
    wps
    cA
    cB
    cP
    @3
    vk
    cJ
    @6
    cX
    wps
    wph
    @0
    @51
    iunconnlem2.2
    syl
    #
    wps
    wph
    @20
    @18
    @51
    iunconnlem2.3
    sylan
    #
    @52
    wps
    wph
    @20
    cJ
    cB
    crest
    co
    cconn
    wcel
    @51
    iunconnlem2.5
    sylan
    #
    wps
    @32
    @21
    @34
    wph
    @21
    @22
    @5
    @8
    @11
    @13
    simp-6r
    syl
    #
    wps
    @32
    @22
    @34
    @24
    @22
    @5
    @8
    @11
    @13
    simp-5r
    syl
    #
    wps
    @32
    @8
    @34
    @26
    @8
    @11
    @13
    simpllr
    syl
    wps
    @32
    @11
    @34
    @27
    @11
    @13
    simplr
    syl
    #
    @35
    @50
    iunconnlem
    wps
    cA
    cB
    cP
    @6
    vk
    cJ
    @3
    cX
    @56
    @57
    @52
    @58
    @60
    @59
    @44
    wps
    @6
    @3
    cin
    @9
    @10
    @6
    @3
    incom
    @61
    syl5eqss
    wps
    @1
    @12
    @6
    @3
    cun
    @35
    @6
    @3
    uncom
    syl6sseqr
    @50
    iunconnlem
    @54
    @55
    wa
    #
    @53
    wi
    @62
    @53
    @29
    @30
    pm4.56
    biimpi
    idiALT
    syl2anc
    sylbir
    pm2.65da
    ex
    ex
    ex3
    3impd
    3expia
    ex
    impd
    ralrimivv
    @0
    @2
    @17
    @16
    vu
    vv
    @1
    cJ
    cX
    connsub
    biimp3ar
    syl3anc
end
