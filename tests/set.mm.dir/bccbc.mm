include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "cbcc.mm"
include "cbc.mm"
include "wceq.mm"
include "wa.mm"
include "cfallfac.mm"
include "cfa.mm"
include "cfv.mm"
include "cdiv.mm"
include "nn0cnd.mm"
include "bccval.mm"
include "adantr.mm"
include "bcfallfac.mm"
include "adantl.mm"
include "eqtr4d.mm"
include "wn.mm"
include "clt.mm"
include "wbr.mm"
include "c1.mm"
include "caddc.mm"
include "cuz.mm"
include "cun.mm"
include "wo.mm"
include "cn0.mm"
include "nn0split.mm"
include "syl.mm"
include "eleqtrd.mm"
include "elun.mm"
include "sylib.mm"
include "orcanai.mm"
include "cle.mm"
include "eluzle.mm"
include "wb.mm"
include "cz.mm"
include "nn0zd.mm"
include "zltp1le.mm"
include "syl2anc.mm"
include "mpbird.mm"
include "syldan.mm"
include "nn0ge0d.mm"
include "cfzo.mm"
include "0zd.mm"
include "elfzo.mm"
include "syl3anc.mm"
include "biimpar.mm"
include "cmin.mm"
include "fzoval.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "bcc0.mm"
include "sylanr1.mm"
include "anabss5.mm"
include "jca.mm"
include "bcval3.mm"
include "3expa.mm"
include "sylan.mm"
include "pm2.61dan.mm"

theorem bccbc
  let wph: wff ph
  let cK: class K
  let cN: class N
  assume bccbc.c: |- ( ph -> N e. NN0 )
  assume bccbc.k: |- ( ph -> K e. NN0 )


  assert |- ( ph -> ( N _Cc K ) = ( N _C K ) )

  proof
    wph
    cK
    cc0
    cN
    cfz
    co
    #
    wcel
    #
    cN
    cK
    cbcc
    co
    #
    cN
    cK
    cbc
    co
    #
    wceq
    wph
    @1
    wa
    @2
    cN
    cK
    cfallfac
    co
    cK
    cfa
    cfv
    cdiv
    co
    #
    @3
    wph
    @2
    @4
    wceq
    @1
    wph
    cN
    cK
    wph
    cN
    bccbc.c
    nn0cnd
    #
    bccbc.k
    bccval
    adantr
    @1
    @3
    @4
    wceq
    wph
    cK
    cN
    bcfallfac
    adantl
    eqtr4d
    wph
    @1
    wn
    #
    wa
    @2
    cc0
    @3
    wph
    @6
    cN
    cK
    clt
    wbr
    #
    @2
    cc0
    wceq
    #
    wph
    @6
    cK
    cN
    c1
    caddc
    co
    #
    cuz
    cfv
    #
    wcel
    #
    @7
    wph
    @1
    @11
    wph
    cK
    @0
    @10
    cun
    #
    wcel
    @1
    @11
    wo
    wph
    cK
    cn0
    @12
    bccbc.k
    wph
    cN
    cn0
    wcel
    #
    cn0
    @12
    wceq
    bccbc.c
    cN
    nn0split
    syl
    eleqtrd
    cK
    @0
    @10
    elun
    sylib
    orcanai
    wph
    @11
    wa
    @7
    @9
    cK
    cle
    wbr
    #
    @11
    @14
    wph
    @9
    cK
    eluzle
    adantl
    wph
    @7
    @14
    wb
    #
    @11
    wph
    cN
    cz
    wcel
    #
    cK
    cz
    wcel
    #
    @15
    wph
    cN
    bccbc.c
    nn0zd
    #
    wph
    cK
    bccbc.k
    nn0zd
    #
    cN
    cK
    zltp1le
    syl2anc
    adantr
    mpbird
    syldan
    wph
    @7
    @8
    wph
    wph
    cc0
    cN
    cle
    wbr
    #
    @7
    @8
    wph
    cN
    bccbc.c
    nn0ge0d
    wph
    @20
    @7
    wa
    #
    cN
    cc0
    cK
    cfzo
    co
    #
    wcel
    #
    @8
    wph
    @23
    @21
    wph
    @16
    cc0
    cz
    wcel
    @17
    @23
    @21
    wb
    @18
    wph
    0zd
    @19
    cN
    cc0
    cK
    elfzo
    syl3anc
    biimpar
    wph
    @23
    cN
    cc0
    cK
    c1
    cmin
    co
    cfz
    co
    #
    wcel
    #
    @8
    wph
    @23
    @25
    wph
    @22
    @24
    cN
    wph
    @17
    @22
    @24
    wceq
    @19
    cc0
    cK
    fzoval
    syl
    eleq2d
    biimpa
    wph
    @8
    @25
    wph
    cN
    cK
    @5
    bccbc.k
    bcc0
    biimpar
    syldan
    syldan
    sylanr1
    anabss5
    syldan
    wph
    @13
    @17
    wa
    @6
    @3
    cc0
    wceq
    #
    wph
    @13
    @17
    bccbc.c
    @19
    jca
    @13
    @17
    @6
    @26
    cK
    cN
    bcval3
    3expa
    sylan
    eqtr4d
    pm2.61dan
end
