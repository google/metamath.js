include "ciun.mm"
include "crest.mm"
include "co.mm"
include "cconn.mm"
include "wcel.mm"
include "cv.mm"
include "cin.mm"
include "c0.mm"
include "wne.mm"
include "cdif.mm"
include "wss.mm"
include "w3a.mm"
include "cun.mm"
include "wn.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "wo.mm"
include "simpr.mm"
include "wrex.mm"
include "simplr1.mm"
include "wex.mm"
include "n0.mm"
include "inss2.mm"
include "sseli.mm"
include "eliun.mm"
include "rexn0.mm"
include "sylbi.mm"
include "syl.mm"
include "exlimiv.mm"
include "simplll.mm"
include "ralrimiva.mm"
include "r19.2z.mm"
include "syl2anc.mm"
include "sylibr.mm"
include "sseldd.mm"
include "elun.mm"
include "sylib.mm"
include "ctopon.mm"
include "cfv.mm"
include "sylan.mm"
include "simpllr.mm"
include "simpld.mm"
include "simprd.mm"
include "simplr2.mm"
include "simplr3.mm"
include "nfv.mm"
include "nfcv.mm"
include "nfiu1.mm"
include "nfin.mm"
include "nfne.mm"
include "nfdif.mm"
include "nfss.mm"
include "nf3an.mm"
include "nfan.mm"
include "nfun.mm"
include "iunconnlem.mm"
include "incom.mm"
include "syl5eqss.mm"
include "uncom.mm"
include "syl6sseq.mm"
include "ioran.mm"
include "sylanbrc.mm"
include "pm2.65da.mm"
include "ex.mm"
include "ralrimivva.mm"
include "wb.mm"
include "iunss.mm"
include "connsub.mm"
include "mpbird.mm"

theorem iunconn
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cP: class P
  let vk: setvar k
  let cJ: class J
  let cX: class X
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let cU: class U
  let cV: class V
  assume iunconn.2: |- ( ph -> J e. ( TopOn ` X ) )
  assume iunconn.3: |- ( ( ph /\ k e. A ) -> B C_ X )
  assume iunconn.4: |- ( ( ph /\ k e. A ) -> P e. B )
  assume iunconn.5: |- ( ( ph /\ k e. A ) -> ( J |`t B ) e. Conn )

  disjoint A k
  disjoint J k
  disjoint P k
  disjoint X k
  disjoint k ph
  disjoint k u
  disjoint k v
  disjoint k x
  disjoint u v
  disjoint u x
  disjoint A u
  disjoint v x
  disjoint A v
  disjoint A x
  disjoint B u
  disjoint B v
  disjoint B x
  disjoint J u
  disjoint J v
  disjoint P x
  disjoint X u
  disjoint X v
  disjoint X x
  disjoint ph u
  disjoint ph v
  disjoint ph x
  disjoint U k
  disjoint U x
  disjoint V k
  disjoint V x
  assert |- ( ph -> ( J |`t U_ k e. A B ) e. Conn )

  proof
    wph
    cJ
    vk
    cA
    cB
    ciun
    #
    crest
    co
    cconn
    wcel
    #
    vu
    cv
    #
    @0
    cin
    #
    c0
    wne
    #
    vv
    cv
    #
    @0
    cin
    #
    c0
    wne
    #
    @2
    @5
    cin
    #
    cX
    @0
    cdif
    #
    wss
    #
    w3a
    #
    @0
    @2
    @5
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
    wph
    @15
    vu
    vv
    cJ
    cJ
    wph
    @2
    cJ
    wcel
    #
    @5
    cJ
    wcel
    #
    wa
    #
    wa
    #
    @11
    @14
    @20
    @11
    wa
    #
    @13
    cP
    @2
    wcel
    #
    cP
    @5
    wcel
    #
    wo
    #
    @21
    @13
    wa
    #
    cP
    @12
    wcel
    @24
    @25
    @0
    @12
    cP
    @21
    @13
    simpr
    #
    @25
    cP
    cB
    wcel
    #
    vk
    cA
    wrex
    #
    cP
    @0
    wcel
    @25
    cA
    c0
    wne
    #
    @27
    vk
    cA
    wral
    #
    @28
    @25
    @4
    @29
    @4
    @7
    @10
    @20
    @13
    simplr1
    #
    @4
    @5
    @3
    wcel
    #
    vv
    wex
    @29
    vv
    @3
    n0
    @32
    @29
    vv
    @32
    @5
    @0
    wcel
    #
    @29
    @3
    @0
    @5
    @2
    @0
    inss2
    sseli
    @33
    @5
    cB
    wcel
    #
    vk
    cA
    wrex
    @29
    vk
    @5
    cA
    cB
    eliun
    @34
    vk
    cA
    rexn0
    sylbi
    syl
    exlimiv
    sylbi
    syl
    @25
    wph
    @30
    wph
    @19
    @11
    @13
    simplll
    #
    wph
    @27
    vk
    cA
    iunconn.4
    ralrimiva
    syl
    @27
    vk
    cA
    r19.2z
    syl2anc
    vk
    cP
    cA
    cB
    eliun
    sylibr
    sseldd
    cP
    @2
    @5
    elun
    sylib
    @25
    @22
    wn
    @23
    wn
    @24
    wn
    @25
    cA
    cB
    cP
    @2
    vk
    cJ
    @5
    cX
    @25
    wph
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    @35
    iunconn.2
    syl
    #
    @25
    wph
    vk
    cv
    cA
    wcel
    #
    cB
    cX
    wss
    #
    @35
    iunconn.3
    sylan
    #
    @25
    wph
    @38
    @27
    @35
    iunconn.4
    sylan
    #
    @25
    wph
    @38
    cJ
    cB
    crest
    co
    cconn
    wcel
    @35
    iunconn.5
    sylan
    #
    @25
    @17
    @18
    wph
    @19
    @11
    @13
    simpllr
    #
    simpld
    #
    @25
    @17
    @18
    @43
    simprd
    #
    @4
    @7
    @10
    @20
    @13
    simplr2
    @4
    @7
    @10
    @20
    @13
    simplr3
    #
    @26
    @21
    @13
    vk
    @20
    @11
    vk
    @20
    vk
    nfv
    @4
    @7
    @10
    vk
    vk
    @3
    c0
    vk
    @2
    @0
    vk
    @2
    nfcv
    #
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
    vk
    @6
    c0
    vk
    @5
    @0
    vk
    @5
    nfcv
    #
    @48
    nfin
    @49
    nfne
    vk
    @8
    @9
    vk
    @8
    nfcv
    vk
    cX
    @0
    vk
    cX
    nfcv
    @48
    nfdif
    nfss
    nf3an
    nfan
    vk
    @0
    @12
    @48
    vk
    @2
    @5
    @47
    @50
    nfun
    nfss
    nfan
    #
    iunconnlem
    @25
    cA
    cB
    cP
    @5
    vk
    cJ
    @2
    cX
    @37
    @40
    @41
    @42
    @45
    @44
    @31
    @25
    @5
    @2
    cin
    @8
    @9
    @5
    @2
    incom
    @46
    syl5eqss
    @25
    @0
    @12
    @5
    @2
    cun
    @26
    @2
    @5
    uncom
    syl6sseq
    @51
    iunconnlem
    @22
    @23
    ioran
    sylanbrc
    pm2.65da
    ex
    ralrimivva
    wph
    @36
    @0
    cX
    wss
    #
    @1
    @16
    wb
    iunconn.2
    wph
    @39
    vk
    cA
    wral
    @52
    wph
    @39
    vk
    cA
    iunconn.3
    ralrimiva
    vk
    cA
    cB
    cX
    iunss
    sylibr
    vu
    vv
    @0
    cJ
    cX
    connsub
    syl2anc
    mpbird
end
