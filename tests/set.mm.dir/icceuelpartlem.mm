include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "wcel.mm"
include "wa.mm"
include "clt.mm"
include "wbr.mm"
include "c1.mm"
include "caddc.mm"
include "cfv.mm"
include "cle.mm"
include "wceq.mm"
include "wo.mm"
include "wi.mm"
include "fveq2.mm"
include "olcd.mm"
include "a1d.mm"
include "wn.mm"
include "cz.mm"
include "elfzoelz.mm"
include "wne.mm"
include "zltp1le.mm"
include "biimpcd.mm"
include "adantr.mm"
include "impcom.mm"
include "df-ne.mm"
include "necom.mm"
include "sylbb1.mm"
include "adantl.mm"
include "jca.mm"
include "cr.mm"
include "wb.mm"
include "peano2z.mm"
include "zred.mm"
include "zre.mm"
include "anim12i.mm"
include "ltlen.mm"
include "syl.mm"
include "mpbird.mm"
include "ex.mm"
include "syl2an.mm"
include "cv.mm"
include "cfz.mm"
include "wral.mm"
include "iccpartgt.mm"
include "fzofzp1.mm"
include "elfzofz.mm"
include "breq1.mm"
include "breq1d.mm"
include "imbi12d.mm"
include "breq2.mm"
include "breq2d.mm"
include "rspc2v.mm"
include "mpan9.mm"
include "syld.mm"
include "expdimp.mm"
include "orcd.mm"
include "pm2.61i.mm"
include "cxr.mm"
include "cn.mm"
include "ciccp.mm"
include "iccpartxr.mm"
include "xrleloe.mm"
include "exp31.mm"

theorem icceuelpartlem
  let wph: wff ph
  let cP: class P
  let cI: class I
  let cJ: class J
  let cM: class M
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vp: setvar p
  let cX: class X
  let vx: setvar x
  assume iccpartiun.m: |- ( ph -> M e. NN )
  assume iccpartiun.p: |- ( ph -> P e. ( RePart ` M ) )


  assert |- ( ph -> ( ( I e. ( 0 ..^ M ) /\ J e. ( 0 ..^ M ) ) -> ( I < J -> ( P ` ( I + 1 ) ) <_ ( P ` J ) ) ) )

  proof
    wph
    cI
    cc0
    cM
    cfzo
    co
    #
    wcel
    #
    cJ
    @0
    wcel
    #
    wa
    #
    cI
    cJ
    clt
    wbr
    #
    cI
    c1
    caddc
    co
    #
    cP
    cfv
    #
    cJ
    cP
    cfv
    #
    cle
    wbr
    #
    wph
    @3
    wa
    #
    @4
    wa
    #
    @8
    @6
    @7
    clt
    wbr
    #
    @6
    @7
    wceq
    #
    wo
    #
    @5
    cJ
    wceq
    #
    @10
    @13
    wi
    @14
    @13
    @10
    @14
    @12
    @11
    @5
    cJ
    cP
    fveq2
    olcd
    a1d
    @14
    wn
    #
    @10
    @13
    @15
    @10
    wa
    @11
    @12
    @10
    @15
    @11
    @9
    @4
    @15
    @11
    @9
    @4
    @15
    wa
    #
    @5
    cJ
    clt
    wbr
    #
    @11
    @3
    @16
    @17
    wi
    #
    wph
    @1
    cI
    cz
    wcel
    #
    cJ
    cz
    wcel
    #
    @18
    @2
    cI
    cc0
    cM
    elfzoelz
    cJ
    cc0
    cM
    elfzoelz
    @19
    @20
    wa
    #
    @16
    @17
    @21
    @16
    wa
    #
    @17
    @5
    cJ
    cle
    wbr
    #
    cJ
    @5
    wne
    #
    wa
    #
    @22
    @23
    @24
    @16
    @21
    @23
    @4
    @21
    @23
    wi
    @15
    @21
    @4
    @23
    cI
    cJ
    zltp1le
    biimpcd
    adantr
    impcom
    @16
    @24
    @21
    @15
    @24
    @4
    @5
    cJ
    wne
    @15
    @24
    @5
    cJ
    df-ne
    @5
    cJ
    necom
    sylbb1
    adantl
    adantl
    jca
    @22
    @5
    cr
    wcel
    #
    cJ
    cr
    wcel
    #
    wa
    #
    @17
    @25
    wb
    @21
    @28
    @16
    @19
    @26
    @20
    @27
    @19
    @5
    cI
    peano2z
    zred
    cJ
    zre
    anim12i
    adantr
    @5
    cJ
    ltlen
    syl
    mpbird
    ex
    syl2an
    adantl
    wph
    vi
    cv
    #
    vj
    cv
    #
    clt
    wbr
    #
    @29
    cP
    cfv
    #
    @30
    cP
    cfv
    #
    clt
    wbr
    #
    wi
    #
    vj
    cc0
    cM
    cfz
    co
    #
    wral
    vi
    @36
    wral
    #
    @3
    @17
    @11
    wi
    #
    wph
    cP
    vi
    vj
    cM
    iccpartiun.m
    iccpartiun.p
    iccpartgt
    @1
    @5
    @36
    wcel
    #
    cJ
    @36
    wcel
    #
    @37
    @38
    wi
    @2
    cc0
    cM
    cI
    fzofzp1
    #
    cJ
    cc0
    cM
    elfzofz
    #
    @35
    @38
    @5
    @30
    clt
    wbr
    #
    @6
    @33
    clt
    wbr
    #
    wi
    vi
    vj
    @5
    cJ
    @36
    @36
    @29
    @5
    wceq
    #
    @31
    @43
    @34
    @44
    @29
    @5
    @30
    clt
    breq1
    @45
    @32
    @6
    @33
    clt
    @29
    @5
    cP
    fveq2
    breq1d
    imbi12d
    @30
    cJ
    wceq
    #
    @43
    @17
    @44
    @11
    @30
    cJ
    @5
    clt
    breq2
    @46
    @33
    @7
    @6
    clt
    @30
    cJ
    cP
    fveq2
    breq2d
    imbi12d
    rspc2v
    syl2an
    mpan9
    syld
    expdimp
    impcom
    orcd
    ex
    pm2.61i
    @10
    @6
    cxr
    wcel
    #
    @7
    cxr
    wcel
    #
    wa
    #
    @8
    @13
    wb
    @9
    @49
    @4
    @9
    @47
    @48
    @9
    cP
    @5
    cM
    wph
    cM
    cn
    wcel
    @3
    iccpartiun.m
    adantr
    #
    wph
    cP
    cM
    ciccp
    cfv
    wcel
    @3
    iccpartiun.p
    adantr
    #
    @3
    @39
    wph
    @1
    @39
    @2
    @41
    adantr
    adantl
    iccpartxr
    @9
    cP
    cJ
    cM
    @50
    @51
    @3
    @40
    wph
    @2
    @40
    @1
    @42
    adantl
    adantl
    iccpartxr
    jca
    adantr
    @6
    @7
    xrleloe
    syl
    mpbird
    exp31
end
