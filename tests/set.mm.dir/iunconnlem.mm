include "cv.mm"
include "ciun.mm"
include "cin.mm"
include "wcel.mm"
include "wex.mm"
include "wn.mm"
include "c0.mm"
include "wne.mm"
include "n0.mm"
include "sylib.mm"
include "wa.mm"
include "elin.mm"
include "wrex.mm"
include "eliun.mm"
include "nfv.mm"
include "nfan.mm"
include "crest.mm"
include "co.mm"
include "cconn.mm"
include "adantr.mm"
include "ctopon.mm"
include "cfv.mm"
include "ad2antrr.mm"
include "wss.mm"
include "simprr.mm"
include "inelcm.mm"
include "syl2anc.mm"
include "ad2antrl.mm"
include "wceq.mm"
include "cdif.mm"
include "ssiun2.mm"
include "ad2antlr.mm"
include "sscond.mm"
include "sstrd.mm"
include "wb.mm"
include "inss1.mm"
include "toponss.mm"
include "syl5ss.mm"
include "reldisj.mm"
include "syl.mm"
include "mpbird.mm"
include "cun.mm"
include "nconnsubb.mm"
include "expr.mm"
include "mt2d.mm"
include "an4s.mm"
include "exp32.mm"
include "rexlimd.mm"
include "syl5bi.mm"
include "expimpd.mm"
include "exlimdv.mm"
include "mpd.mm"

theorem iunconnlem
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cP: class P
  let cU: class U
  let vk: setvar k
  let cJ: class J
  let cV: class V
  let cX: class X
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  assume iunconn.2: |- ( ph -> J e. ( TopOn ` X ) )
  assume iunconn.3: |- ( ( ph /\ k e. A ) -> B C_ X )
  assume iunconn.4: |- ( ( ph /\ k e. A ) -> P e. B )
  assume iunconn.5: |- ( ( ph /\ k e. A ) -> ( J |`t B ) e. Conn )
  assume iunconn.6: |- ( ph -> U e. J )
  assume iunconn.7: |- ( ph -> V e. J )
  assume iunconn.8: |- ( ph -> ( V i^i U_ k e. A B ) =/= (/) )
  assume iunconn.9: |- ( ph -> ( U i^i V ) C_ ( X \ U_ k e. A B ) )
  assume iunconn.10: |- ( ph -> U_ k e. A B C_ ( U u. V ) )
  assume iunconn.11: |- F/ k ph

  disjoint A k
  disjoint J k
  disjoint P k
  disjoint X k
  disjoint U k
  disjoint V k
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
  disjoint U x
  disjoint V x
  assert |- ( ph -> -. P e. U )

  proof
    wph
    vx
    cv
    #
    cV
    vk
    cA
    cB
    ciun
    #
    cin
    #
    wcel
    #
    vx
    wex
    #
    cP
    cU
    wcel
    #
    wn
    #
    wph
    @2
    c0
    wne
    @4
    iunconn.8
    vx
    @2
    n0
    sylib
    wph
    @3
    @6
    vx
    @3
    @0
    cV
    wcel
    #
    @0
    @1
    wcel
    #
    wa
    wph
    @6
    @0
    cV
    @1
    elin
    wph
    @7
    @8
    @6
    @8
    @0
    cB
    wcel
    #
    vk
    cA
    wrex
    wph
    @7
    wa
    #
    @6
    vk
    @0
    cA
    cB
    eliun
    @10
    @9
    @6
    vk
    cA
    wph
    @7
    vk
    iunconn.11
    @7
    vk
    nfv
    nfan
    @6
    vk
    nfv
    @10
    vk
    cv
    cA
    wcel
    #
    @9
    @6
    wph
    @11
    @7
    @9
    @6
    wph
    @11
    wa
    #
    @7
    @9
    wa
    #
    wa
    @5
    cJ
    cB
    crest
    co
    cconn
    wcel
    #
    @12
    @14
    @13
    iunconn.5
    adantr
    @12
    @13
    @5
    @14
    wn
    @12
    @13
    @5
    wa
    #
    wa
    #
    cB
    cU
    cJ
    cV
    cX
    wph
    cJ
    cX
    ctopon
    cfv
    wcel
    #
    @11
    @15
    iunconn.2
    ad2antrr
    #
    @12
    cB
    cX
    wss
    @15
    iunconn.3
    adantr
    wph
    cU
    cJ
    wcel
    #
    @11
    @15
    iunconn.6
    ad2antrr
    #
    wph
    cV
    cJ
    wcel
    @11
    @15
    iunconn.7
    ad2antrr
    @16
    @5
    cP
    cB
    wcel
    #
    cU
    cB
    cin
    c0
    wne
    @12
    @13
    @5
    simprr
    @12
    @21
    @15
    iunconn.4
    adantr
    cP
    cU
    cB
    inelcm
    syl2anc
    @13
    cV
    cB
    cin
    c0
    wne
    @12
    @5
    @0
    cV
    cB
    inelcm
    ad2antrl
    @16
    cU
    cV
    cin
    #
    cB
    cin
    c0
    wceq
    #
    @22
    cX
    cB
    cdif
    #
    wss
    #
    @16
    @22
    cX
    @1
    cdif
    #
    @24
    wph
    @22
    @26
    wss
    @11
    @15
    iunconn.9
    ad2antrr
    @16
    cB
    @1
    cX
    @11
    cB
    @1
    wss
    wph
    @15
    vk
    cA
    cB
    ssiun2
    ad2antlr
    #
    sscond
    sstrd
    @16
    @22
    cX
    wss
    @23
    @25
    wb
    @16
    @22
    cU
    cX
    cU
    cV
    inss1
    @16
    @17
    @19
    cU
    cX
    wss
    @18
    @20
    cU
    cJ
    cX
    toponss
    syl2anc
    syl5ss
    @22
    cB
    cX
    reldisj
    syl
    mpbird
    @16
    cB
    @1
    cU
    cV
    cun
    #
    @27
    wph
    @1
    @28
    wss
    @11
    @15
    iunconn.10
    ad2antrr
    sstrd
    nconnsubb
    expr
    mt2d
    an4s
    exp32
    rexlimd
    syl5bi
    expimpd
    syl5bi
    exlimdv
    mpd
end
