include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "csupp.mm"
include "co.mm"
include "wss.mm"
include "wi.mm"
include "cv.mm"
include "cfv.mm"
include "wne.mm"
include "wfn.mm"
include "wb.mm"
include "wf.mm"
include "ffn.mm"
include "syl.mm"
include "adantl.mm"
include "cdm.mm"
include "wceq.mm"
include "fdm.mm"
include "dmexg.mm"
include "adantr.mm"
include "eleq1.mm"
include "eqcoms.mm"
include "syl5ibr.mm"
include "3syl.mm"
include "impcom.mm"
include "simplr.mm"
include "elsuppfn.mm"
include "syl3anc.mm"
include "wn.mm"
include "cdif.mm"
include "eldif.mm"
include "adantll.mm"
include "sylan2br.mm"
include "expr.mm"
include "necon1ad.mm"
include "expimpd.mm"
include "sylbid.mm"
include "ssrdv.mm"
include "ex.mm"
include "c0.mm"
include "supp0prc.mm"
include "0ss.mm"
include "syl6eqss.mm"
include "a1d.mm"
include "pm2.61i.mm"

theorem suppss
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cF: class F
  let cW: class W
  let cZ: class Z
  assume suppss.f: |- ( ph -> F : A --> B )
  assume suppss.n: |- ( ( ph /\ k e. ( A \ W ) ) -> ( F ` k ) = Z )

  disjoint F k
  disjoint k ph
  disjoint W k
  disjoint Z k
  assert |- ( ph -> ( F supp Z ) C_ W )

  proof
    cF
    cvv
    wcel
    #
    cZ
    cvv
    wcel
    #
    wa
    #
    wph
    cF
    cZ
    csupp
    co
    #
    cW
    wss
    #
    wi
    @2
    wph
    @4
    @2
    wph
    wa
    #
    vk
    @3
    cW
    @5
    vk
    cv
    #
    @3
    wcel
    #
    @6
    cA
    wcel
    #
    @6
    cF
    cfv
    #
    cZ
    wne
    #
    wa
    #
    @6
    cW
    wcel
    #
    @5
    cF
    cA
    wfn
    #
    cA
    cvv
    wcel
    #
    @1
    @7
    @11
    wb
    wph
    @13
    @2
    wph
    cA
    cB
    cF
    wf
    #
    @13
    suppss.f
    cA
    cB
    cF
    ffn
    syl
    adantl
    wph
    @2
    @14
    wph
    @15
    cF
    cdm
    #
    cA
    wceq
    #
    @2
    @14
    wi
    suppss.f
    cA
    cB
    cF
    fdm
    @2
    @14
    @17
    @16
    cvv
    wcel
    #
    @0
    @18
    @1
    cF
    cvv
    dmexg
    adantr
    @14
    @18
    wb
    cA
    @16
    cA
    @16
    cvv
    eleq1
    eqcoms
    syl5ibr
    3syl
    impcom
    @0
    @1
    wph
    simplr
    @6
    cF
    cvv
    cvv
    cA
    cZ
    elsuppfn
    syl3anc
    @5
    @8
    @10
    @12
    @5
    @8
    wa
    @12
    @9
    cZ
    @5
    @8
    @12
    wn
    #
    @9
    cZ
    wceq
    #
    @8
    @19
    wa
    @5
    @6
    cA
    cW
    cdif
    wcel
    #
    @20
    @6
    cA
    cW
    eldif
    wph
    @21
    @20
    @2
    suppss.n
    adantll
    sylan2br
    expr
    necon1ad
    expimpd
    sylbid
    ssrdv
    ex
    @2
    wn
    #
    @4
    wph
    @22
    @3
    c0
    cW
    cF
    cZ
    supp0prc
    cW
    0ss
    syl6eqss
    a1d
    pm2.61i
end
