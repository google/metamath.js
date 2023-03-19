include "cc0.mm"
include "cfv.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "wceq.mm"
include "c1.mm"
include "wo.mm"
include "csn.mm"
include "caddc.mm"
include "cun.mm"
include "cuz.mm"
include "cn0.mm"
include "nnnn0d.mm"
include "elnn0uz.mm"
include "sylib.mm"
include "fzpred.mm"
include "syl.mm"
include "eleq2d.mm"
include "wb.mm"
include "elun.mm"
include "a1i.mm"
include "velsn.mm"
include "0p1e1.mm"
include "oveq1d.mm"
include "orbi12d.mm"
include "3bitrd.mm"
include "wi.mm"
include "cxr.mm"
include "0elfz.mm"
include "iccpartxr.mm"
include "xrleid.mm"
include "fveq2.mm"
include "breq2d.mm"
include "syl5ibr.mm"
include "wa.mm"
include "clt.mm"
include "wral.mm"
include "iccpartgtl.mm"
include "weq.mm"
include "rspccv.mm"
include "imp.mm"
include "adantr.mm"
include "cn.mm"
include "ciccp.mm"
include "wss.mm"
include "1nn0.mm"
include "fzss1.mm"
include "sselda.mm"
include "xrltle.mm"
include "syl2anc.mm"
include "mpd.mm"
include "expcom.mm"
include "jaoi.mm"
include "com12.mm"
include "sylbid.mm"
include "ralrimiv.mm"

theorem iccpartgel
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
  assert |- ( ph -> A. i e. ( 0 ... M ) ( P ` 0 ) <_ ( P ` i ) )

  proof
    wph
    cc0
    cP
    cfv
    #
    vi
    cv
    #
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
    @1
    @4
    wcel
    #
    @1
    cc0
    wceq
    #
    @1
    c1
    cM
    cfz
    co
    #
    wcel
    #
    wo
    #
    @3
    wph
    @5
    @1
    cc0
    csn
    #
    cc0
    c1
    caddc
    co
    #
    cM
    cfz
    co
    #
    cun
    #
    wcel
    #
    @1
    @10
    wcel
    #
    @1
    @12
    wcel
    #
    wo
    #
    @9
    wph
    @4
    @13
    @1
    wph
    cM
    cc0
    cuz
    cfv
    #
    wcel
    #
    @4
    @13
    wceq
    wph
    cM
    cn0
    wcel
    #
    @19
    wph
    cM
    iccpartgtprec.m
    nnnn0d
    #
    cM
    elnn0uz
    sylib
    cc0
    cM
    fzpred
    syl
    eleq2d
    @14
    @17
    wb
    wph
    @1
    @10
    @12
    elun
    a1i
    wph
    @15
    @6
    @16
    @8
    @15
    @6
    wb
    wph
    vi
    cc0
    velsn
    a1i
    wph
    @12
    @7
    @1
    wph
    @11
    c1
    cM
    cfz
    @11
    c1
    wceq
    wph
    0p1e1
    a1i
    oveq1d
    eleq2d
    orbi12d
    3bitrd
    @9
    wph
    @3
    @6
    wph
    @3
    wi
    @8
    wph
    @3
    @6
    @0
    @0
    cle
    wbr
    #
    wph
    @0
    cxr
    wcel
    #
    @22
    wph
    cP
    cc0
    cM
    iccpartgtprec.m
    iccpartgtprec.p
    wph
    @20
    cc0
    @4
    wcel
    @21
    cM
    0elfz
    syl
    iccpartxr
    #
    @0
    xrleid
    syl
    @6
    @2
    @0
    @0
    cle
    @1
    cc0
    cP
    fveq2
    breq2d
    syl5ibr
    wph
    @8
    @3
    wph
    @8
    wa
    #
    @0
    @2
    clt
    wbr
    #
    @3
    wph
    @8
    @26
    wph
    @0
    vk
    cv
    #
    cP
    cfv
    #
    clt
    wbr
    #
    vk
    @7
    wral
    @8
    @26
    wi
    wph
    cP
    vk
    cM
    iccpartgtprec.m
    iccpartgtprec.p
    iccpartgtl
    @29
    @26
    vk
    @1
    @7
    vk
    vi
    weq
    @28
    @2
    @0
    clt
    @27
    @1
    cP
    fveq2
    breq2d
    rspccv
    syl
    imp
    @25
    @23
    @2
    cxr
    wcel
    @26
    @3
    wi
    wph
    @23
    @8
    @24
    adantr
    @25
    cP
    @1
    cM
    wph
    cM
    cn
    wcel
    @8
    iccpartgtprec.m
    adantr
    wph
    cP
    cM
    ciccp
    cfv
    wcel
    @8
    iccpartgtprec.p
    adantr
    wph
    @7
    @4
    @1
    wph
    c1
    @18
    wcel
    #
    @7
    @4
    wss
    wph
    c1
    cn0
    wcel
    #
    @30
    @31
    wph
    1nn0
    a1i
    c1
    elnn0uz
    sylib
    c1
    cc0
    cM
    fzss1
    syl
    sselda
    iccpartxr
    @0
    @2
    xrltle
    syl2anc
    mpd
    expcom
    jaoi
    com12
    sylbid
    ralrimiv
end
