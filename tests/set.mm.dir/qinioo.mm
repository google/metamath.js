include "cq.mm"
include "cioo.mm"
include "co.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "wn.mm"
include "simplr.mm"
include "clt.mm"
include "wne.mm"
include "xrltnled.mm"
include "biimpar.mm"
include "cv.mm"
include "wcel.mm"
include "wrex.mm"
include "cxr.mm"
include "adantr.mm"
include "simpr.mm"
include "qbtwnxr.mm"
include "syl3anc.mm"
include "wi.mm"
include "ad2antrr.mm"
include "cr.mm"
include "qre.mm"
include "ad2antlr.mm"
include "simprl.mm"
include "simprr.mm"
include "eliood.mm"
include "ex.mm"
include "adantlr.mm"
include "reximdva.mm"
include "mpd.mm"
include "inn0.mm"
include "sylibr.mm"
include "syldan.mm"
include "neneqd.mm"
include "condan.mm"
include "wb.mm"
include "ioo0.mm"
include "syl2anc.mm"
include "ineq2.mm"
include "in0.mm"
include "syl6eq.mm"
include "syl.mm"
include "impbida.mm"

theorem qinioo
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vq: setvar q
  assume qinioo.a: |- ( ph -> A e. RR* )
  assume qinioo.b: |- ( ph -> B e. RR* )


  assert |- ( ph -> ( ( QQ i^i ( A (,) B ) ) = (/) <-> B <_ A ) )

  proof
    wph
    cq
    cA
    cB
    cioo
    co
    #
    cin
    #
    c0
    wceq
    #
    cB
    cA
    cle
    wbr
    #
    wph
    @2
    wa
    @3
    @2
    wph
    @2
    @3
    wn
    #
    simplr
    wph
    @4
    @2
    wn
    @2
    wph
    @4
    wa
    @1
    c0
    wph
    @4
    cA
    cB
    clt
    wbr
    #
    @1
    c0
    wne
    #
    wph
    @5
    @4
    wph
    cA
    cB
    qinioo.a
    qinioo.b
    xrltnled
    biimpar
    wph
    @5
    wa
    #
    vq
    cv
    #
    @0
    wcel
    #
    vq
    cq
    wrex
    #
    @6
    @7
    cA
    @8
    clt
    wbr
    #
    @8
    cB
    clt
    wbr
    #
    wa
    #
    vq
    cq
    wrex
    #
    @10
    @7
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    @5
    @14
    wph
    @15
    @5
    qinioo.a
    adantr
    wph
    @16
    @5
    qinioo.b
    adantr
    wph
    @5
    simpr
    vq
    cA
    cB
    qbtwnxr
    syl3anc
    @7
    @13
    @9
    vq
    cq
    wph
    @8
    cq
    wcel
    #
    @13
    @9
    wi
    @5
    wph
    @17
    wa
    #
    @13
    @9
    @18
    @13
    wa
    cA
    cB
    @8
    wph
    @15
    @17
    @13
    qinioo.a
    ad2antrr
    wph
    @16
    @17
    @13
    qinioo.b
    ad2antrr
    @17
    @8
    cr
    wcel
    wph
    @13
    @8
    qre
    ad2antlr
    @18
    @11
    @12
    simprl
    @18
    @11
    @12
    simprr
    eliood
    ex
    adantlr
    reximdva
    mpd
    vq
    cq
    @0
    inn0
    sylibr
    syldan
    neneqd
    adantlr
    condan
    wph
    @3
    wa
    @0
    c0
    wceq
    #
    @2
    wph
    @19
    @3
    wph
    @15
    @16
    @19
    @3
    wb
    qinioo.a
    qinioo.b
    cA
    cB
    ioo0
    syl2anc
    biimpar
    @19
    @1
    cq
    c0
    cin
    c0
    @0
    c0
    cq
    ineq2
    cq
    in0
    syl6eq
    syl
    impbida
end
