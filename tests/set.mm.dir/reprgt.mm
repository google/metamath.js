include "crepr.mm"
include "cfv.mm"
include "co.mm"
include "cc0.mm"
include "cfzo.mm"
include "cv.mm"
include "csu.mm"
include "wceq.mm"
include "cmap.mm"
include "crab.mm"
include "c0.mm"
include "c1.mm"
include "cfz.mm"
include "cn.mm"
include "fz1ssnn.mm"
include "syl6ss.mm"
include "reprval.mm"
include "wn.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "cfn.mm"
include "fzofi.mm"
include "a1i.mm"
include "cr.mm"
include "wss.mm"
include "nnssre.mm"
include "ralrimivw.mm"
include "r19.21bi.mm"
include "wf.mm"
include "cvv.mm"
include "ovex.mm"
include "ssexd.mm"
include "adantr.mm"
include "elexi.mm"
include "simpr.mm"
include "elmapg.mm"
include "biimpa.mm"
include "syl21anc.mm"
include "ffvelrnd.mm"
include "sseldd.mm"
include "fsumrecl.mm"
include "cmul.mm"
include "nn0red.mm"
include "remulcld.mm"
include "zred.mm"
include "cle.mm"
include "ad2antrr.mm"
include "wbr.mm"
include "elfzle2.mm"
include "syl.mm"
include "fsumle.mm"
include "chash.mm"
include "cc.mm"
include "recnd.mm"
include "fsumconst.mm"
include "sylancr.mm"
include "cn0.mm"
include "hashfzo0.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "breqtrd.mm"
include "clt.mm"
include "lelttrd.mm"
include "ltned.mm"
include "neneqd.mm"
include "ralrimiva.mm"
include "rabeq0.mm"
include "sylibr.mm"

theorem reprgt
  let wph: wff ph
  let cA: class A
  let cS: class S
  let cM: class M
  let cN: class N
  let va: setvar a
  let vc: setvar c
  assume reprgt.n: |- ( ph -> N e. NN0 )
  assume reprgt.a: |- ( ph -> A C_ ( 1 ... N ) )
  assume reprgt.m: |- ( ph -> M e. ZZ )
  assume reprgt.s: |- ( ph -> S e. NN0 )
  assume reprgt.1: |- ( ph -> ( S x. N ) < M )


  assert |- ( ph -> ( A ( repr ` S ) M ) = (/) )

  proof
    wph
    cA
    cM
    cS
    crepr
    cfv
    co
    cc0
    cS
    cfzo
    co
    #
    va
    cv
    #
    vc
    cv
    #
    cfv
    #
    va
    csu
    #
    cM
    wceq
    #
    vc
    cA
    @0
    cmap
    co
    #
    crab
    #
    c0
    wph
    cA
    cS
    cM
    va
    vc
    wph
    cA
    c1
    cN
    cfz
    co
    #
    cn
    reprgt.a
    cN
    fz1ssnn
    syl6ss
    #
    reprgt.m
    reprgt.s
    reprval
    wph
    @5
    wn
    #
    vc
    @6
    wral
    @7
    c0
    wceq
    wph
    @10
    vc
    @6
    wph
    @2
    @6
    wcel
    #
    wa
    #
    @4
    cM
    @12
    @4
    cM
    @12
    @0
    @3
    va
    @0
    cfn
    wcel
    #
    @12
    cc0
    cS
    fzofi
    #
    a1i
    #
    @12
    @1
    @0
    wcel
    #
    wa
    #
    cA
    cr
    @3
    @12
    cA
    cr
    wss
    #
    va
    @0
    wph
    @18
    va
    @0
    wral
    #
    vc
    @6
    wph
    @19
    vc
    @6
    wph
    @18
    va
    @0
    wph
    cA
    cn
    cr
    @9
    nnssre
    syl6ss
    ralrimivw
    ralrimivw
    r19.21bi
    r19.21bi
    @17
    @0
    cA
    @1
    @2
    @12
    @0
    cA
    @2
    wf
    #
    @16
    @12
    cA
    cvv
    wcel
    #
    @0
    cvv
    wcel
    #
    @11
    @20
    wph
    @21
    @11
    wph
    cA
    @8
    cvv
    @8
    cvv
    wcel
    wph
    c1
    cN
    cfz
    ovex
    a1i
    reprgt.a
    ssexd
    adantr
    @22
    @12
    @0
    cfn
    @14
    elexi
    a1i
    wph
    @11
    simpr
    @21
    @22
    wa
    @11
    @20
    cA
    @0
    @2
    cvv
    cvv
    elmapg
    biimpa
    syl21anc
    adantr
    @12
    @16
    simpr
    ffvelrnd
    #
    sseldd
    #
    fsumrecl
    #
    @12
    @4
    cS
    cN
    cmul
    co
    #
    cM
    @25
    @12
    cS
    cN
    wph
    cS
    cr
    wcel
    @11
    wph
    cS
    reprgt.s
    nn0red
    adantr
    wph
    cN
    cr
    wcel
    #
    @11
    wph
    cN
    reprgt.n
    nn0red
    #
    adantr
    remulcld
    wph
    cM
    cr
    wcel
    @11
    wph
    cM
    reprgt.m
    zred
    adantr
    @12
    @4
    @0
    cN
    va
    csu
    #
    @26
    cle
    @12
    @0
    @3
    cN
    va
    @15
    @24
    wph
    @27
    @11
    @16
    @28
    ad2antrr
    @17
    @3
    @8
    wcel
    @3
    cN
    cle
    wbr
    @17
    cA
    @8
    @3
    wph
    cA
    @8
    wss
    @11
    @16
    reprgt.a
    ad2antrr
    @23
    sseldd
    @3
    c1
    cN
    elfzle2
    syl
    fsumle
    wph
    @29
    @26
    wceq
    @11
    wph
    @29
    @0
    chash
    cfv
    #
    cN
    cmul
    co
    #
    @26
    wph
    @13
    cN
    cc
    wcel
    @29
    @31
    wceq
    @14
    wph
    cN
    @28
    recnd
    @0
    cN
    va
    fsumconst
    sylancr
    wph
    @30
    cS
    cN
    cmul
    wph
    cS
    cn0
    wcel
    @30
    cS
    wceq
    reprgt.s
    cS
    hashfzo0
    syl
    oveq1d
    eqtrd
    adantr
    breqtrd
    wph
    @26
    cM
    clt
    wbr
    @11
    reprgt.1
    adantr
    lelttrd
    ltned
    neneqd
    ralrimiva
    @5
    vc
    @6
    rabeq0
    sylibr
    eqtrd
end
