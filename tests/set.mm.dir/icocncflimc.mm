include "cfv.mm"
include "climc.mm"
include "co.mm"
include "cioo.mm"
include "cres.mm"
include "cico.mm"
include "cc.mm"
include "rexrd.mm"
include "leidd.mm"
include "elicod.mm"
include "cnlimci.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "csn.mm"
include "cun.mm"
include "crest.mm"
include "wf.mm"
include "cv.mm"
include "ccnp.mm"
include "wcel.mm"
include "wral.mm"
include "ccn.mm"
include "wa.mm"
include "ccncf.mm"
include "wss.mm"
include "wceq.mm"
include "cncfrss.mm"
include "syl.mm"
include "ssid.mm"
include "eqid.mm"
include "cncfcn.mm"
include "sylancl.mm"
include "eleqtrd.mm"
include "ctopon.mm"
include "wb.mm"
include "cnfldtopon.mm"
include "a1i.mm"
include "resttopon.mm"
include "syl2anc.mm"
include "ctop.mm"
include "cnfldtop.mm"
include "unicntop.mm"
include "restid.mm"
include "ax-mp.mm"
include "cncnp.mm"
include "mpbid.mm"
include "simpld.mm"
include "ioossico.mm"
include "cnt.mm"
include "cdif.mm"
include "cin.mm"
include "recnd.mm"
include "ntrtop.mm"
include "undif.mm"
include "sylib.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "syl5eqr.mm"
include "elind.mm"
include "restntr.mm"
include "syl3anc.mm"
include "eleqtrrd.mm"
include "snssd.mm"
include "ssequn2.mm"
include "oveq2d.mm"
include "cxr.mm"
include "clt.mm"
include "wbr.mm"
include "snunioo1.mm"
include "fveq12d.mm"
include "limcres.mm"

theorem icocncflimc
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  let vx: setvar x
  let vk: setvar k
  assume icocncflimc.a: |- ( ph -> A e. RR )
  assume icocncflimc.b: |- ( ph -> B e. RR* )
  assume icocncflimc.altb: |- ( ph -> A < B )
  assume icocncflimc.f: |- ( ph -> F e. ( ( A [,) B ) -cn-> CC ) )


  assert |- ( ph -> ( F ` A ) e. ( ( F |` ( A (,) B ) ) limCC A ) )

  proof
    wph
    cA
    cF
    cfv
    cF
    cA
    climc
    co
    cF
    cA
    cB
    cioo
    co
    #
    cres
    cA
    climc
    co
    wph
    cA
    cB
    cico
    co
    #
    cA
    cc
    cF
    icocncflimc.f
    wph
    cA
    cB
    cA
    wph
    cA
    icocncflimc.a
    rexrd
    #
    icocncflimc.b
    @2
    wph
    cA
    icocncflimc.a
    leidd
    icocncflimc.altb
    elicod
    #
    cnlimci
    wph
    @1
    cA
    @0
    cF
    ccnfld
    ctopn
    cfv
    #
    @1
    cA
    csn
    #
    cun
    #
    crest
    co
    #
    @4
    wph
    @1
    cc
    cF
    wf
    #
    cF
    vx
    cv
    @4
    @1
    crest
    co
    #
    @4
    cc
    crest
    co
    #
    ccnp
    co
    cfv
    wcel
    vx
    @1
    wral
    #
    wph
    cF
    @9
    @10
    ccn
    co
    #
    wcel
    #
    @8
    @11
    wa
    #
    wph
    cF
    @1
    cc
    ccncf
    co
    #
    @12
    icocncflimc.f
    wph
    @1
    cc
    wss
    #
    cc
    cc
    wss
    @15
    @12
    wceq
    wph
    cF
    @15
    wcel
    @16
    icocncflimc.f
    @1
    cc
    cF
    cncfrss
    syl
    #
    cc
    ssid
    @1
    cc
    @4
    @9
    @10
    @4
    eqid
    #
    @9
    eqid
    #
    @10
    eqid
    cncfcn
    sylancl
    eleqtrd
    wph
    @9
    @1
    ctopon
    cfv
    wcel
    #
    @10
    cc
    ctopon
    cfv
    #
    wcel
    @13
    @14
    wb
    wph
    @4
    @21
    wcel
    #
    @16
    @20
    @22
    wph
    @4
    @18
    cnfldtopon
    a1i
    @17
    @1
    @4
    cc
    resttopon
    syl2anc
    @10
    @4
    ctop
    wcel
    #
    @10
    @4
    wceq
    @4
    @18
    cnfldtop
    #
    @4
    ctop
    cc
    unicntop
    restid
    ax-mp
    cnfldtopon
    vx
    cF
    @9
    @10
    @1
    cc
    cncnp
    sylancl
    mpbid
    simpld
    @0
    @1
    wss
    wph
    cA
    cB
    ioossico
    a1i
    @17
    @18
    @7
    eqid
    wph
    cA
    @1
    @9
    cnt
    cfv
    #
    cfv
    #
    @0
    @5
    cun
    #
    @7
    cnt
    cfv
    #
    cfv
    wph
    cA
    @1
    cc
    @1
    cdif
    cun
    #
    @4
    cnt
    cfv
    #
    cfv
    #
    @1
    cin
    #
    @26
    wph
    @31
    @1
    cA
    wph
    cA
    cc
    @31
    wph
    cA
    icocncflimc.a
    recnd
    wph
    cc
    cc
    @30
    cfv
    #
    @31
    @23
    @33
    cc
    wceq
    @24
    @4
    cc
    unicntop
    ntrtop
    ax-mp
    wph
    cc
    @29
    @30
    wph
    @29
    cc
    wph
    @16
    @29
    cc
    wceq
    @17
    @1
    cc
    undif
    sylib
    eqcomd
    fveq2d
    syl5eqr
    eleqtrd
    @3
    elind
    wph
    @23
    @16
    @1
    @1
    wss
    #
    @26
    @32
    wceq
    @23
    wph
    @24
    a1i
    @17
    @34
    wph
    @1
    ssid
    a1i
    @1
    @4
    @9
    cc
    @1
    unicntop
    @19
    restntr
    syl3anc
    eleqtrrd
    wph
    @1
    @27
    @25
    @28
    wph
    @9
    @7
    cnt
    wph
    @1
    @6
    @4
    crest
    wph
    @6
    @1
    wph
    @5
    @1
    wss
    @6
    @1
    wceq
    wph
    cA
    @1
    @3
    snssd
    @5
    @1
    ssequn2
    sylib
    eqcomd
    oveq2d
    fveq2d
    wph
    @27
    @1
    wph
    cA
    cxr
    wcel
    cB
    cxr
    wcel
    cA
    cB
    clt
    wbr
    @27
    @1
    wceq
    @2
    icocncflimc.b
    icocncflimc.altb
    cA
    cB
    snunioo1
    syl3anc
    eqcomd
    fveq12d
    eleqtrd
    limcres
    eleqtrrd
end
