include "crn.mm"
include "cc0.mm"
include "cfv.mm"
include "cicc.mm"
include "co.mm"
include "cv.mm"
include "wcel.mm"
include "wceq.mm"
include "cfz.mm"
include "wrex.mm"
include "wfn.mm"
include "wb.mm"
include "ciccp.mm"
include "cxr.mm"
include "cmap.mm"
include "c1.mm"
include "caddc.mm"
include "clt.mm"
include "wbr.mm"
include "cfzo.mm"
include "wral.mm"
include "wa.mm"
include "cn.mm"
include "iccpart.mm"
include "syl.mm"
include "elmapfn.mm"
include "adantr.mm"
include "syl6bi.mm"
include "mpd.mm"
include "fvelrnb.mm"
include "cle.mm"
include "simpr.mm"
include "iccpartxr.mm"
include "wi.mm"
include "iccpartgel.mm"
include "weq.mm"
include "fveq2.mm"
include "breq2d.mm"
include "rspcva.mm"
include "expcom.mm"
include "imp.mm"
include "iccpartleu.mm"
include "breq1d.mm"
include "w3a.mm"
include "cn0.mm"
include "nnnn0.mm"
include "0elfz.mm"
include "3syl.mm"
include "nn0fz0.mm"
include "sylib.mm"
include "jca.mm"
include "elicc1.mm"
include "mpbir3and.mm"
include "eleq1.mm"
include "syl5ibcom.mm"
include "rexlimdva.mm"
include "sylbid.mm"
include "ssrdv.mm"

theorem iccpartrn
  let wph: wff ph
  let cP: class P
  let cM: class M
  let vi: setvar i
  let vk: setvar k
  let vp: setvar p
  let vx: setvar x
  assume iccpartgtprec.m: |- ( ph -> M e. NN )
  assume iccpartgtprec.p: |- ( ph -> P e. ( RePart ` M ) )


  assert |- ( ph -> ran P C_ ( ( P ` 0 ) [,] ( P ` M ) ) )

  proof
    wph
    vp
    cP
    crn
    #
    cc0
    cP
    cfv
    #
    cM
    cP
    cfv
    #
    cicc
    co
    #
    wph
    vp
    cv
    #
    @0
    wcel
    #
    vi
    cv
    #
    cP
    cfv
    #
    @4
    wceq
    #
    vi
    cc0
    cM
    cfz
    co
    #
    wrex
    #
    @4
    @3
    wcel
    #
    wph
    cP
    @9
    wfn
    #
    @5
    @10
    wb
    wph
    cP
    cM
    ciccp
    cfv
    wcel
    #
    @12
    iccpartgtprec.p
    wph
    @13
    cP
    cxr
    @9
    cmap
    co
    wcel
    #
    @7
    @6
    c1
    caddc
    co
    cP
    cfv
    clt
    wbr
    vi
    cc0
    cM
    cfzo
    co
    wral
    #
    wa
    #
    @12
    wph
    cM
    cn
    wcel
    #
    @13
    @16
    wb
    iccpartgtprec.m
    cP
    vi
    cM
    iccpart
    syl
    @14
    @12
    @15
    cP
    cxr
    @9
    elmapfn
    adantr
    syl6bi
    mpd
    vi
    @9
    @4
    cP
    fvelrnb
    syl
    wph
    @8
    @11
    vi
    @9
    wph
    @6
    @9
    wcel
    #
    wa
    #
    @7
    @3
    wcel
    #
    @8
    @11
    @19
    @20
    @7
    cxr
    wcel
    #
    @1
    @7
    cle
    wbr
    #
    @7
    @2
    cle
    wbr
    #
    @19
    cP
    @6
    cM
    wph
    @17
    @18
    iccpartgtprec.m
    adantr
    wph
    @13
    @18
    iccpartgtprec.p
    adantr
    wph
    @18
    simpr
    iccpartxr
    wph
    @18
    @22
    wph
    @1
    vk
    cv
    #
    cP
    cfv
    #
    cle
    wbr
    #
    vk
    @9
    wral
    #
    @18
    @22
    wi
    wph
    cP
    vk
    cM
    iccpartgtprec.m
    iccpartgtprec.p
    iccpartgel
    @18
    @27
    @22
    @26
    @22
    vk
    @6
    @9
    vk
    vi
    weq
    #
    @25
    @7
    @1
    cle
    @24
    @6
    cP
    fveq2
    #
    breq2d
    rspcva
    expcom
    syl
    imp
    wph
    @18
    @23
    wph
    @25
    @2
    cle
    wbr
    #
    vk
    @9
    wral
    #
    @18
    @23
    wi
    wph
    cP
    vk
    cM
    iccpartgtprec.m
    iccpartgtprec.p
    iccpartleu
    @18
    @31
    @23
    @30
    @23
    vk
    @6
    @9
    @28
    @25
    @7
    @2
    cle
    @29
    breq1d
    rspcva
    expcom
    syl
    imp
    @19
    @1
    cxr
    wcel
    #
    @2
    cxr
    wcel
    #
    wa
    #
    @20
    @21
    @22
    @23
    w3a
    wb
    wph
    @34
    @18
    wph
    @32
    @33
    wph
    cP
    cc0
    cM
    iccpartgtprec.m
    iccpartgtprec.p
    wph
    @17
    cM
    cn0
    wcel
    #
    cc0
    @9
    wcel
    iccpartgtprec.m
    cM
    nnnn0
    #
    cM
    0elfz
    3syl
    iccpartxr
    wph
    cP
    cM
    cM
    iccpartgtprec.m
    iccpartgtprec.p
    wph
    @17
    cM
    @9
    wcel
    #
    iccpartgtprec.m
    @17
    @35
    @37
    @36
    cM
    nn0fz0
    sylib
    syl
    iccpartxr
    jca
    adantr
    @1
    @2
    @7
    elicc1
    syl
    mpbir3and
    @7
    @4
    @3
    eleq1
    syl5ibcom
    rexlimdva
    sylbid
    ssrdv
end
