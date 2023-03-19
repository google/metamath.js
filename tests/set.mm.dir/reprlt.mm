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
include "reprval.mm"
include "wn.mm"
include "wral.mm"
include "wcel.mm"
include "wa.mm"
include "cr.mm"
include "zred.mm"
include "adantr.mm"
include "nn0red.mm"
include "cfn.mm"
include "fzofi.mm"
include "a1i.mm"
include "wss.mm"
include "cn.mm"
include "nnssre.mm"
include "sstrd.mm"
include "ad2antrr.mm"
include "wf.mm"
include "cvv.mm"
include "nnex.mm"
include "ssexd.mm"
include "elexi.mm"
include "simpr.mm"
include "elmapg.mm"
include "biimpa.mm"
include "syl21anc.mm"
include "ffvelrnd.mm"
include "sseldd.mm"
include "fsumrecl.mm"
include "clt.mm"
include "wbr.mm"
include "c1.mm"
include "cle.mm"
include "chash.mm"
include "cmul.mm"
include "cc.mm"
include "ax-1cn.mm"
include "fsumconst.mm"
include "mp2an.mm"
include "cn0.mm"
include "hashcl.mm"
include "ax-mp.mm"
include "nn0cni.mm"
include "mulid1i.mm"
include "eqtri.mm"
include "hashfzo0.mm"
include "syl.mm"
include "syl5eq.mm"
include "1red.mm"
include "nnge1.mm"
include "fsumle.mm"
include "eqbrtrrd.mm"
include "ltletrd.mm"
include "ltned.mm"
include "necomd.mm"
include "neneqd.mm"
include "ralrimiva.mm"
include "rabeq0.mm"
include "sylibr.mm"
include "eqtrd.mm"

theorem reprlt
  let wph: wff ph
  let cA: class A
  let cS: class S
  let cM: class M
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vm: setvar m
  let vs: setvar s
  assume reprval.a: |- ( ph -> A C_ NN )
  assume reprval.m: |- ( ph -> M e. ZZ )
  assume reprval.s: |- ( ph -> S e. NN0 )
  assume reprlt.1: |- ( ph -> M < S )


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
    reprval.a
    reprval.m
    reprval.s
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
    @8
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
    @10
    cM
    @4
    @10
    cM
    @4
    wph
    cM
    cr
    wcel
    @9
    wph
    cM
    reprval.m
    zred
    adantr
    #
    @10
    cM
    cS
    @4
    @11
    wph
    cS
    cr
    wcel
    @9
    wph
    cS
    reprval.s
    nn0red
    adantr
    @10
    @0
    @3
    va
    @0
    cfn
    wcel
    #
    @10
    cc0
    cS
    fzofi
    #
    a1i
    #
    @10
    @1
    @0
    wcel
    #
    wa
    #
    cA
    cr
    @3
    wph
    cA
    cr
    wss
    @9
    @15
    wph
    cA
    cn
    cr
    reprval.a
    cn
    cr
    wss
    wph
    nnssre
    a1i
    sstrd
    ad2antrr
    @16
    @0
    cA
    @1
    @2
    @10
    @0
    cA
    @2
    wf
    #
    @15
    @10
    cA
    cvv
    wcel
    #
    @0
    cvv
    wcel
    #
    @9
    @17
    wph
    @18
    @9
    wph
    cA
    cn
    cvv
    cn
    cvv
    wcel
    wph
    nnex
    a1i
    reprval.a
    ssexd
    adantr
    @19
    @10
    @0
    cfn
    @13
    elexi
    a1i
    wph
    @9
    simpr
    @18
    @19
    wa
    @9
    @17
    cA
    @0
    @2
    cvv
    cvv
    elmapg
    biimpa
    syl21anc
    adantr
    @10
    @15
    simpr
    ffvelrnd
    #
    sseldd
    #
    fsumrecl
    wph
    cM
    cS
    clt
    wbr
    @9
    reprlt.1
    adantr
    @10
    @0
    c1
    va
    csu
    #
    cS
    @4
    cle
    wph
    @22
    cS
    wceq
    @9
    wph
    @22
    @0
    chash
    cfv
    #
    cS
    @22
    @23
    c1
    cmul
    co
    #
    @23
    @12
    c1
    cc
    wcel
    @22
    @24
    wceq
    @13
    ax-1cn
    @0
    c1
    va
    fsumconst
    mp2an
    @23
    @23
    @12
    @23
    cn0
    wcel
    @13
    @0
    hashcl
    ax-mp
    nn0cni
    mulid1i
    eqtri
    wph
    cS
    cn0
    wcel
    @23
    cS
    wceq
    reprval.s
    cS
    hashfzo0
    syl
    syl5eq
    adantr
    @10
    @0
    c1
    @3
    va
    @14
    @16
    1red
    @21
    @16
    @3
    cn
    wcel
    c1
    @3
    cle
    wbr
    @16
    cA
    cn
    @3
    wph
    cA
    cn
    wss
    @9
    @15
    reprval.a
    ad2antrr
    @20
    sseldd
    @3
    nnge1
    syl
    fsumle
    eqbrtrrd
    ltletrd
    ltned
    necomd
    neneqd
    ralrimiva
    @5
    vc
    @6
    rabeq0
    sylibr
    eqtrd
end
