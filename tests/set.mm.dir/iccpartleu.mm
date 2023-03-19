include "cv.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "cfzo.mm"
include "wceq.mm"
include "wo.mm"
include "csn.mm"
include "cun.mm"
include "cuz.mm"
include "cn.mm"
include "cn0.mm"
include "nnnn0.mm"
include "elnn0uz.mm"
include "sylib.mm"
include "syl.mm"
include "fzisfzounsn.mm"
include "eleq2d.mm"
include "wb.mm"
include "elun.mm"
include "a1i.mm"
include "velsn.mm"
include "orbi2d.mm"
include "3bitrd.mm"
include "wi.mm"
include "wa.mm"
include "clt.mm"
include "wral.mm"
include "iccpartltu.mm"
include "weq.mm"
include "fveq2.mm"
include "breq1d.mm"
include "rspccv.mm"
include "imp.mm"
include "cxr.mm"
include "adantr.mm"
include "ciccp.mm"
include "wss.mm"
include "fzossfz.mm"
include "sselda.mm"
include "iccpartxr.mm"
include "nn0fz0.mm"
include "xrltle.mm"
include "syl2anc.mm"
include "mpd.mm"
include "expcom.mm"
include "xrleid.mm"
include "adantl.mm"
include "eqbrtrd.mm"
include "ex.mm"
include "jaoi.mm"
include "com12.mm"
include "sylbid.mm"
include "ralrimiv.mm"

theorem iccpartleu
  let wph: wff ph
  let cP: class P
  let vi: setvar i
  let cM: class M
  let vk: setvar k
  let vx: setvar x
  assume iccpartgtprec.m: |- ( ph -> M e. NN )
  assume iccpartgtprec.p: |- ( ph -> P e. ( RePart ` M ) )

  disjoint M i
  disjoint P i
  disjoint i ph
  disjoint M k
  disjoint i k
  disjoint P k
  disjoint k ph
  disjoint k x
  assert |- ( ph -> A. i e. ( 0 ... M ) ( P ` i ) <_ ( P ` M ) )

  proof
    wph
    vi
    cv
    #
    cP
    cfv
    #
    cM
    cP
    cfv
    #
    cle
    wbr
    #
    vi
    cc0
    cM
    cfz
    co
    #
    wph
    @0
    @4
    wcel
    #
    @0
    cc0
    cM
    cfzo
    co
    #
    wcel
    #
    @0
    cM
    wceq
    #
    wo
    #
    @3
    wph
    @5
    @0
    @6
    cM
    csn
    #
    cun
    #
    wcel
    #
    @7
    @0
    @10
    wcel
    #
    wo
    #
    @9
    wph
    @4
    @11
    @0
    wph
    cM
    cc0
    cuz
    cfv
    wcel
    #
    @4
    @11
    wceq
    wph
    cM
    cn
    wcel
    #
    @15
    iccpartgtprec.m
    @16
    cM
    cn0
    wcel
    #
    @15
    cM
    nnnn0
    #
    cM
    elnn0uz
    sylib
    syl
    cc0
    cM
    fzisfzounsn
    syl
    eleq2d
    @12
    @14
    wb
    wph
    @0
    @6
    @10
    elun
    a1i
    wph
    @13
    @8
    @7
    @13
    @8
    wb
    wph
    vi
    cM
    velsn
    a1i
    orbi2d
    3bitrd
    @9
    wph
    @3
    @7
    wph
    @3
    wi
    @8
    wph
    @7
    @3
    wph
    @7
    wa
    #
    @1
    @2
    clt
    wbr
    #
    @3
    wph
    @7
    @20
    wph
    vk
    cv
    #
    cP
    cfv
    #
    @2
    clt
    wbr
    #
    vk
    @6
    wral
    @7
    @20
    wi
    wph
    cP
    vk
    cM
    iccpartgtprec.m
    iccpartgtprec.p
    iccpartltu
    @23
    @20
    vk
    @0
    @6
    vk
    vi
    weq
    @22
    @1
    @2
    clt
    @21
    @0
    cP
    fveq2
    breq1d
    rspccv
    syl
    imp
    @19
    @1
    cxr
    wcel
    @2
    cxr
    wcel
    #
    @20
    @3
    wi
    @19
    cP
    @0
    cM
    wph
    @16
    @7
    iccpartgtprec.m
    adantr
    wph
    cP
    cM
    ciccp
    cfv
    wcel
    @7
    iccpartgtprec.p
    adantr
    wph
    @6
    @4
    @0
    @6
    @4
    wss
    wph
    cc0
    cM
    fzossfz
    a1i
    sselda
    iccpartxr
    wph
    @24
    @7
    wph
    cP
    cM
    cM
    iccpartgtprec.m
    iccpartgtprec.p
    wph
    @16
    cM
    @4
    wcel
    #
    iccpartgtprec.m
    @16
    @17
    @25
    @18
    cM
    nn0fz0
    sylib
    syl
    iccpartxr
    #
    adantr
    @1
    @2
    xrltle
    syl2anc
    mpd
    expcom
    @8
    wph
    @3
    @8
    wph
    wa
    @1
    @2
    @2
    cle
    @8
    @1
    @2
    wceq
    wph
    @0
    cM
    cP
    fveq2
    adantr
    wph
    @2
    @2
    cle
    wbr
    #
    @8
    wph
    @24
    @27
    @26
    @2
    xrleid
    syl
    adantl
    eqbrtrd
    ex
    jaoi
    com12
    sylbid
    ralrimiv
end
