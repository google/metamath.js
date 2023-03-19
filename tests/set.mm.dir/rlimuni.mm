include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "c2.mm"
include "cdiv.mm"
include "clt.mm"
include "wa.mm"
include "wi.mm"
include "wral.mm"
include "cr.mm"
include "wrex.mm"
include "wn.mm"
include "wceq.mm"
include "wcel.mm"
include "cc.mm"
include "crli.mm"
include "rlimcl.mm"
include "syl.mm"
include "ad2antrr.mm"
include "subcld.mm"
include "abscld.mm"
include "ltnrd.mm"
include "ffvelrnda.mm"
include "adantlr.mm"
include "abssubd.mm"
include "breq1d.mm"
include "anbi1d.mm"
include "abs3lem.mm"
include "syl22anc.mm"
include "sylbid.mm"
include "imim2d.mm"
include "com23.mm"
include "impd.mm"
include "mtod.mm"
include "nrexdv.mm"
include "r19.29r.mm"
include "nsyl.mm"
include "cxr.mm"
include "csup.mm"
include "cpnf.mm"
include "wss.mm"
include "wb.mm"
include "cdm.mm"
include "wf.mm"
include "fdm.mm"
include "rlimss.mm"
include "eqsstr3d.mm"
include "ressxr.mm"
include "syl6ss.mm"
include "supxrunb1.mm"
include "mpbird.mm"
include "r19.29.mm"
include "ex.mm"
include "wne.mm"
include "adantr.mm"
include "ffvelrn.mm"
include "ralrimiva.mm"
include "simpr.mm"
include "subne0d.mm"
include "absrpcld.mm"
include "rphalfcld.mm"
include "cmpt.mm"
include "feqmptd.mm"
include "eqbrtrrd.mm"
include "rlimi.mm"
include "rexanre.mm"
include "mpbir2and.mm"
include "necon1bd.mm"
include "mpd.mm"

theorem rlimuni
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let vj: setvar j
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y
  assume rlimuni.1: |- ( ph -> F : A --> CC )
  assume rlimuni.2: |- ( ph -> sup ( A , RR* , < ) = +oo )
  assume rlimuni.3: |- ( ph -> F ~~>r B )
  assume rlimuni.4: |- ( ph -> F ~~>r C )


  assert |- ( ph -> B = C )

  proof
    wph
    vj
    cv
    #
    vk
    cv
    #
    cle
    wbr
    #
    @1
    cF
    cfv
    #
    cB
    cmin
    co
    cabs
    cfv
    #
    cB
    cC
    cmin
    co
    #
    cabs
    cfv
    #
    c2
    cdiv
    co
    #
    clt
    wbr
    #
    @3
    cC
    cmin
    co
    cabs
    cfv
    @7
    clt
    wbr
    #
    wa
    #
    wi
    #
    vk
    cA
    wral
    #
    vj
    cr
    wrex
    #
    wn
    cB
    cC
    wceq
    wph
    @13
    @2
    vk
    cA
    wrex
    #
    @12
    wa
    #
    vj
    cr
    wrex
    #
    wph
    @15
    vj
    cr
    wph
    @0
    cr
    wcel
    #
    wa
    #
    @2
    @11
    wa
    #
    vk
    cA
    wrex
    @15
    @18
    @19
    vk
    cA
    @18
    @1
    cA
    wcel
    #
    wa
    #
    @19
    @6
    @6
    clt
    wbr
    #
    @21
    @6
    @21
    @5
    @21
    cB
    cC
    wph
    cB
    cc
    wcel
    #
    @17
    @20
    wph
    cF
    cB
    crli
    wbr
    #
    @23
    rlimuni.3
    cB
    cF
    rlimcl
    syl
    #
    ad2antrr
    #
    wph
    cC
    cc
    wcel
    #
    @17
    @20
    wph
    cF
    cC
    crli
    wbr
    #
    @27
    rlimuni.4
    cC
    cF
    rlimcl
    syl
    #
    ad2antrr
    #
    subcld
    abscld
    #
    ltnrd
    @21
    @2
    @11
    @22
    @21
    @11
    @2
    @22
    @21
    @10
    @22
    @2
    @21
    @10
    cB
    @3
    cmin
    co
    cabs
    cfv
    #
    @7
    clt
    wbr
    #
    @9
    wa
    #
    @22
    @21
    @8
    @33
    @9
    @21
    @4
    @32
    @7
    clt
    @21
    @3
    cB
    wph
    @20
    @3
    cc
    wcel
    #
    @17
    wph
    cA
    cc
    @1
    cF
    rlimuni.1
    ffvelrnda
    adantlr
    #
    @26
    abssubd
    breq1d
    anbi1d
    @21
    @23
    @27
    @35
    @6
    cr
    wcel
    @34
    @22
    wi
    @26
    @30
    @36
    @31
    cB
    cC
    @3
    @6
    abs3lem
    syl22anc
    sylbid
    imim2d
    com23
    impd
    mtod
    nrexdv
    @2
    @11
    vk
    cA
    r19.29r
    nsyl
    nrexdv
    wph
    @14
    vj
    cr
    wral
    #
    @13
    @16
    wi
    wph
    @37
    cA
    cxr
    clt
    csup
    cpnf
    wceq
    #
    rlimuni.2
    wph
    cA
    cxr
    wss
    @37
    @38
    wb
    wph
    cA
    cr
    cxr
    wph
    cA
    cF
    cdm
    #
    cr
    wph
    cA
    cc
    cF
    wf
    #
    @39
    cA
    wceq
    rlimuni.1
    cA
    cc
    cF
    fdm
    syl
    wph
    @24
    @39
    cr
    wss
    rlimuni.3
    cB
    cF
    rlimss
    syl
    eqsstr3d
    #
    ressxr
    syl6ss
    vj
    vk
    cA
    supxrunb1
    syl
    mpbird
    @37
    @13
    @16
    @14
    @12
    vj
    cr
    r19.29
    ex
    syl
    mtod
    wph
    @13
    cB
    cC
    wph
    cB
    cC
    wne
    #
    @13
    wph
    @42
    wa
    #
    @13
    @2
    @8
    wi
    vk
    cA
    wral
    vj
    cr
    wrex
    #
    @2
    @9
    wi
    vk
    cA
    wral
    vj
    cr
    wrex
    #
    @43
    vj
    vk
    cA
    @3
    cB
    @7
    cc
    @43
    @40
    @35
    vk
    cA
    wral
    wph
    @40
    @42
    rlimuni.1
    adantr
    #
    @40
    @35
    vk
    cA
    cA
    cc
    @1
    cF
    ffvelrn
    ralrimiva
    syl
    #
    @43
    @6
    @43
    @5
    @43
    cB
    cC
    wph
    @23
    @42
    @25
    adantr
    #
    wph
    @27
    @42
    @29
    adantr
    #
    subcld
    @43
    cB
    cC
    @48
    @49
    wph
    @42
    simpr
    subne0d
    absrpcld
    rphalfcld
    #
    @43
    cF
    vk
    cA
    @3
    cmpt
    #
    cB
    crli
    @43
    vk
    cA
    cc
    cF
    @46
    feqmptd
    #
    wph
    @24
    @42
    rlimuni.3
    adantr
    eqbrtrrd
    rlimi
    @43
    vj
    vk
    cA
    @3
    cC
    @7
    cc
    @47
    @50
    @43
    cF
    @51
    cC
    crli
    @52
    wph
    @28
    @42
    rlimuni.4
    adantr
    eqbrtrrd
    rlimi
    @43
    cA
    cr
    wss
    #
    @13
    @44
    @45
    wa
    wb
    wph
    @53
    @42
    @41
    adantr
    @8
    @9
    cA
    vj
    vk
    rexanre
    syl
    mpbir2and
    ex
    necon1bd
    mpd
end
