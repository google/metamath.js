include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "nfv.mm"
include "cuni.mm"
include "cc0.mm"
include "wne.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "cmpt.mm"
include "cdm.mm"
include "cr.mm"
include "eqid.mm"
include "dmmptdf.mm"
include "eqcomd.mm"
include "smfdmss.mm"
include "eqsstrd.mm"
include "syl5ss.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "1red.mm"
include "sseli.mm"
include "adantl.mm"
include "syldan.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "rabidim2.mm"
include "syl.mm"
include "redivcld.mm"
include "clt.mm"
include "wbr.mm"
include "crest.mm"
include "cun.mm"
include "nfan.mm"
include "ad4ant14.mm"
include "crp.mm"
include "simpl.mm"
include "simpr.mm"
include "elrpd.mm"
include "adantll.mm"
include "pimrecltpos.mm"
include "csalg.mm"
include "cvv.mm"
include "rabexd.mm"
include "subsalsal.mm"
include "ad2antrr.mm"
include "adantr.mm"
include "csmblfn.mm"
include "cfv.mm"
include "wss.mm"
include "a1i.mm"
include "sssmfmpt.mm"
include "rprecred.mm"
include "smfpimgtmpt.mm"
include "0red.mm"
include "smfpimltmpt.mm"
include "saluncld.mm"
include "eqeltrd.mm"
include "wn.mm"
include "wceq.mm"
include "wb.mm"
include "breq2.mm"
include "ad2antlr.mm"
include "reclt0.mm"
include "bicomd.mm"
include "adantlr.mm"
include "bitrd.mm"
include "rabbida.mm"
include "simpll.mm"
include "neqne.mm"
include "simplr.mm"
include "lttri5d.mm"
include "adantlll.mm"
include "cioo.mm"
include "sylan2.mm"
include "pimrecltneg.mm"
include "lt0ne0.mm"
include "rexrd.mm"
include "smfpimioompt.mm"
include "syl2anc.mm"
include "pm2.61dan.mm"
include "issmfdmpt.mm"

theorem smfrec
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cS: class S
  let cV: class V
  let va: setvar a
  let vk: setvar k
  assume smfrec.x: |- F/ x ph
  assume smfrec.s: |- ( ph -> S e. SAlg )
  assume smfrec.a: |- ( ph -> A e. V )
  assume smfrec.b: |- ( ( ph /\ x e. A ) -> B e. RR )
  assume smfrec.m: |- ( ph -> ( x e. A |-> B ) e. ( SMblFn ` S ) )
  assume smfrec.e: |- C = { x e. A | B =/= 0 }

  disjoint A x
  disjoint C x
  disjoint B a
  disjoint C a
  disjoint a x
  disjoint S a
  disjoint a ph
  disjoint k x
  assert |- ( ph -> ( x e. C |-> ( 1 / B ) ) e. ( SMblFn ` S ) )

  proof
    wph
    vx
    cC
    c1
    cB
    cdiv
    co
    #
    cS
    va
    smfrec.x
    wph
    va
    nfv
    smfrec.s
    wph
    cC
    cA
    cS
    cuni
    #
    cC
    cB
    cc0
    wne
    #
    vx
    cA
    crab
    #
    cA
    smfrec.e
    @2
    vx
    cA
    ssrab2
    eqsstri
    #
    wph
    cA
    vx
    cA
    cB
    cmpt
    #
    cdm
    #
    @1
    wph
    @6
    cA
    wph
    vx
    @5
    cA
    cB
    cr
    smfrec.x
    @5
    eqid
    smfrec.b
    dmmptdf
    eqcomd
    wph
    @6
    cS
    @5
    smfrec.s
    smfrec.m
    @6
    eqid
    smfdmss
    eqsstrd
    syl5ss
    wph
    vx
    cv
    #
    cC
    wcel
    #
    wa
    #
    c1
    cB
    @9
    1red
    wph
    @8
    @7
    cA
    wcel
    #
    cB
    cr
    wcel
    #
    @8
    @10
    wph
    cC
    cA
    @7
    @4
    sseli
    #
    adantl
    smfrec.b
    syldan
    #
    @8
    @2
    wph
    @8
    @7
    @3
    wcel
    #
    @2
    @8
    @14
    cC
    @3
    @7
    smfrec.e
    eleq2i
    biimpi
    @2
    vx
    cA
    rabidim2
    syl
    #
    adantl
    #
    redivcld
    wph
    va
    cv
    #
    cr
    wcel
    #
    wa
    #
    cc0
    @17
    clt
    wbr
    #
    @0
    @17
    clt
    wbr
    #
    vx
    cC
    crab
    #
    cS
    cC
    crest
    co
    #
    wcel
    #
    @19
    @20
    wa
    #
    @22
    c1
    @17
    cdiv
    co
    #
    cB
    clt
    wbr
    vx
    cC
    crab
    #
    cB
    cc0
    clt
    wbr
    #
    vx
    cC
    crab
    #
    cun
    @23
    @25
    vx
    cC
    cB
    @17
    @19
    @20
    vx
    wph
    @18
    vx
    smfrec.x
    @18
    vx
    nfv
    nfan
    #
    @20
    vx
    nfv
    nfan
    #
    wph
    @8
    @11
    @18
    @20
    @13
    ad4ant14
    #
    @8
    @2
    @25
    @15
    adantl
    @18
    @20
    @17
    crp
    wcel
    wph
    @18
    @20
    wa
    #
    @17
    @18
    @20
    simpl
    @18
    @20
    simpr
    elrpd
    #
    adantll
    pimrecltpos
    @25
    @23
    @27
    @29
    wph
    @23
    csalg
    wcel
    @18
    @20
    wph
    cC
    cS
    @23
    cvv
    smfrec.s
    wph
    @2
    vx
    cA
    cC
    cV
    smfrec.e
    smfrec.a
    rabexd
    #
    @23
    eqid
    subsalsal
    ad2antrr
    @25
    vx
    cC
    cB
    cS
    @26
    cr
    @31
    @19
    cS
    csalg
    wcel
    #
    @20
    wph
    @36
    @18
    smfrec.s
    adantr
    #
    adantr
    @32
    @19
    vx
    cC
    cB
    cmpt
    cS
    csmblfn
    cfv
    wcel
    #
    @20
    wph
    @38
    @18
    wph
    vx
    cA
    cB
    cC
    cS
    smfrec.s
    smfrec.m
    cC
    cA
    wss
    wph
    @4
    a1i
    sssmfmpt
    #
    adantr
    #
    adantr
    @18
    @20
    @26
    cr
    wcel
    #
    wph
    @33
    @17
    @34
    rprecred
    adantll
    smfpimgtmpt
    wph
    @29
    @23
    wcel
    #
    @18
    @20
    wph
    vx
    cC
    cB
    cc0
    cS
    cr
    smfrec.x
    smfrec.s
    @13
    @39
    wph
    0red
    #
    smfpimltmpt
    #
    ad2antrr
    saluncld
    eqeltrd
    @19
    @20
    wn
    #
    wa
    #
    @17
    cc0
    wceq
    #
    @24
    wph
    @47
    @24
    @18
    @45
    wph
    @47
    wa
    #
    @22
    @29
    @23
    @48
    @21
    @28
    vx
    cC
    wph
    @47
    vx
    smfrec.x
    @47
    vx
    nfv
    nfan
    @48
    @8
    wa
    @21
    @0
    cc0
    clt
    wbr
    #
    @28
    @47
    @21
    @49
    wb
    wph
    @8
    @17
    cc0
    @0
    clt
    breq2
    ad2antlr
    wph
    @8
    @49
    @28
    wb
    @47
    @9
    @28
    @49
    @9
    cB
    @13
    @16
    reclt0
    bicomd
    adantlr
    bitrd
    rabbida
    wph
    @42
    @47
    @44
    adantr
    eqeltrd
    ad4ant14
    @46
    @47
    wn
    #
    wa
    @19
    @17
    cc0
    clt
    wbr
    #
    @24
    @19
    @45
    @50
    simpll
    @18
    @45
    @50
    @51
    wph
    @18
    @45
    wa
    #
    @50
    wa
    #
    @17
    cc0
    @18
    @45
    @50
    simpll
    @53
    0red
    @50
    @17
    cc0
    wne
    @52
    @17
    cc0
    neqne
    adantl
    @18
    @45
    @50
    simplr
    lttri5d
    adantlll
    @19
    @51
    wa
    #
    @22
    cB
    @26
    cc0
    cioo
    co
    wcel
    vx
    cC
    crab
    @23
    @54
    vx
    cC
    cB
    @17
    @19
    @51
    vx
    @30
    @51
    vx
    nfv
    nfan
    #
    @19
    @8
    @11
    @51
    @8
    @19
    @10
    @11
    @12
    wph
    @10
    @11
    @18
    smfrec.b
    adantlr
    sylan2
    adantlr
    #
    @8
    @2
    @54
    @15
    adantl
    @19
    @18
    @51
    wph
    @18
    simpr
    adantr
    @19
    @51
    simpr
    pimrecltneg
    @54
    vx
    cC
    cB
    cc0
    cS
    @26
    cvv
    cr
    @55
    @19
    @36
    @51
    @37
    adantr
    wph
    cC
    cvv
    wcel
    @18
    @51
    @35
    ad2antrr
    @56
    @19
    @38
    @51
    @40
    adantr
    @54
    @26
    @18
    @51
    @41
    wph
    @18
    @51
    wa
    #
    c1
    @17
    @57
    1red
    @18
    @51
    simpl
    @17
    lt0ne0
    redivcld
    adantll
    rexrd
    @54
    cc0
    wph
    cc0
    cr
    wcel
    @18
    @51
    @43
    ad2antrr
    rexrd
    smfpimioompt
    eqeltrd
    syl2anc
    pm2.61dan
    pm2.61dan
    issmfdmpt
end
