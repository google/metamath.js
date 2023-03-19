include "c1.mm"
include "wceq.mm"
include "cc0.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "wi.mm"
include "wa.mm"
include "caddc.mm"
include "co.mm"
include "cxr.mm"
include "cfz.mm"
include "cmap.mm"
include "wcel.mm"
include "cn.mm"
include "ciccp.mm"
include "cfzo.mm"
include "lbfzo0.mm"
include "sylibr.mm"
include "iccpartimp.mm"
include "syl3anc.mm"
include "simprd.mm"
include "adantl.mm"
include "fveq2.mm"
include "1e0p1.mm"
include "fveq2i.mm"
include "syl6eq.mm"
include "adantr.mm"
include "breqtrrd.mm"
include "ex.mm"
include "wn.mm"
include "cv.mm"
include "wral.mm"
include "iccpartiltu.mm"
include "iccpartigtl.mm"
include "1nn.mm"
include "a1i.mm"
include "wne.mm"
include "df-ne.mm"
include "cle.mm"
include "nnge1d.mm"
include "1red.mm"
include "nnred.mm"
include "ltlend.mm"
include "biimprd.mm"
include "mpand.mm"
include "syl5bir.mm"
include "imp.mm"
include "elfzo1.mm"
include "syl3anbrc.mm"
include "breq2d.mm"
include "rspcv.mm"
include "syl.mm"
include "breq1d.mm"
include "cn0.mm"
include "nnnn0.mm"
include "0elfz.mm"
include "3syl.mm"
include "iccpartxr.mm"
include "1nn0.mm"
include "elfz2nn0.mm"
include "nn0fz0.mm"
include "sylib.mm"
include "xrlttr.mm"
include "expcomd.mm"
include "syld.mm"
include "com23.mm"
include "com24.mm"
include "mp2d.mm"
include "com12.mm"
include "pm2.61i.mm"

theorem iccpartlt
  let wph: wff ph
  let cP: class P
  let cM: class M
  let vi: setvar i
  let vk: setvar k
  let vx: setvar x
  assume iccpartgtprec.m: |- ( ph -> M e. NN )
  assume iccpartgtprec.p: |- ( ph -> P e. ( RePart ` M ) )


  assert |- ( ph -> ( P ` 0 ) < ( P ` M ) )

  proof
    cM
    c1
    wceq
    #
    wph
    cc0
    cP
    cfv
    #
    cM
    cP
    cfv
    #
    clt
    wbr
    #
    wi
    @0
    wph
    @3
    @0
    wph
    wa
    @1
    cc0
    c1
    caddc
    co
    #
    cP
    cfv
    #
    @2
    clt
    wph
    @1
    @5
    clt
    wbr
    #
    @0
    wph
    cP
    cxr
    cc0
    cM
    cfz
    co
    #
    cmap
    co
    wcel
    #
    @6
    wph
    cM
    cn
    wcel
    #
    cP
    cM
    ciccp
    cfv
    wcel
    #
    cc0
    cc0
    cM
    cfzo
    co
    wcel
    #
    @8
    @6
    wa
    iccpartgtprec.m
    iccpartgtprec.p
    wph
    @9
    @11
    iccpartgtprec.m
    cM
    lbfzo0
    sylibr
    cP
    cc0
    cM
    iccpartimp
    syl3anc
    simprd
    adantl
    @0
    @2
    @5
    wceq
    wph
    @0
    @2
    c1
    cP
    cfv
    #
    @5
    cM
    c1
    cP
    fveq2
    c1
    @4
    cP
    1e0p1
    fveq2i
    syl6eq
    adantr
    breqtrrd
    ex
    wph
    @0
    wn
    #
    @3
    wph
    vi
    cv
    #
    cP
    cfv
    #
    @2
    clt
    wbr
    #
    vi
    c1
    cM
    cfzo
    co
    #
    wral
    #
    @1
    @15
    clt
    wbr
    #
    vi
    @17
    wral
    #
    @13
    @3
    wi
    wph
    cP
    vi
    cM
    iccpartgtprec.m
    iccpartgtprec.p
    iccpartiltu
    wph
    cP
    vi
    cM
    iccpartgtprec.m
    iccpartgtprec.p
    iccpartigtl
    wph
    @13
    @20
    @18
    @3
    wph
    @13
    @20
    @18
    @3
    wi
    #
    wi
    wph
    @13
    wa
    #
    @20
    @1
    @12
    clt
    wbr
    #
    @21
    @22
    c1
    @17
    wcel
    #
    @20
    @23
    wi
    @22
    c1
    cn
    wcel
    #
    @9
    c1
    cM
    clt
    wbr
    #
    @24
    @25
    @22
    1nn
    a1i
    wph
    @9
    @13
    iccpartgtprec.m
    adantr
    #
    wph
    @13
    @26
    @13
    cM
    c1
    wne
    #
    wph
    @26
    cM
    c1
    df-ne
    wph
    c1
    cM
    cle
    wbr
    #
    @28
    @26
    wph
    cM
    iccpartgtprec.m
    nnge1d
    #
    wph
    @26
    @29
    @28
    wa
    wph
    c1
    cM
    wph
    1red
    wph
    cM
    iccpartgtprec.m
    nnred
    ltlend
    biimprd
    mpand
    syl5bir
    imp
    cM
    c1
    elfzo1
    syl3anbrc
    #
    @19
    @23
    vi
    c1
    @17
    @14
    c1
    wceq
    #
    @15
    @12
    @1
    clt
    @14
    c1
    cP
    fveq2
    #
    breq2d
    rspcv
    syl
    @22
    @18
    @23
    @3
    @22
    @18
    @12
    @2
    clt
    wbr
    #
    @23
    @3
    wi
    @22
    @24
    @18
    @34
    wi
    @31
    @16
    @34
    vi
    c1
    @17
    @32
    @15
    @12
    @2
    clt
    @33
    breq1d
    rspcv
    syl
    @22
    @23
    @34
    @3
    @22
    @1
    cxr
    wcel
    #
    @12
    cxr
    wcel
    @2
    cxr
    wcel
    #
    @23
    @34
    wa
    @3
    wi
    wph
    @35
    @13
    wph
    cP
    cc0
    cM
    iccpartgtprec.m
    iccpartgtprec.p
    wph
    @9
    cM
    cn0
    wcel
    #
    cc0
    @7
    wcel
    iccpartgtprec.m
    cM
    nnnn0
    #
    cM
    0elfz
    3syl
    iccpartxr
    adantr
    @22
    cP
    c1
    cM
    @27
    wph
    @10
    @13
    iccpartgtprec.p
    adantr
    @22
    c1
    cn0
    wcel
    #
    @37
    @29
    c1
    @7
    wcel
    @39
    @22
    1nn0
    a1i
    wph
    @37
    @13
    wph
    @9
    @37
    iccpartgtprec.m
    @38
    syl
    adantr
    wph
    @29
    @13
    @30
    adantr
    c1
    cM
    elfz2nn0
    syl3anbrc
    iccpartxr
    wph
    @36
    @13
    wph
    cP
    cM
    cM
    iccpartgtprec.m
    iccpartgtprec.p
    wph
    @9
    cM
    @7
    wcel
    #
    iccpartgtprec.m
    @9
    @37
    @40
    @38
    cM
    nn0fz0
    sylib
    syl
    iccpartxr
    adantr
    @1
    @12
    @2
    xrlttr
    syl3anc
    expcomd
    syld
    com23
    syld
    ex
    com24
    mp2d
    com12
    pm2.61i
end
