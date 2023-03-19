include "cfv.mm"
include "climc.mm"
include "co.mm"
include "cioo.mm"
include "cres.mm"
include "cioc.mm"
include "cc.mm"
include "rexrd.mm"
include "leidd.mm"
include "eliocd.mm"
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
include "resttopon.mm"
include "sylancr.mm"
include "ctop.mm"
include "cnfldtop.mm"
include "unicntop.mm"
include "restid.mm"
include "ax-mp.mm"
include "cncnp.mm"
include "mpbid.mm"
include "simpld.mm"
include "ioossioc.mm"
include "a1i.mm"
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
include "snunioo2.mm"
include "fveq12d.mm"
include "limcres.mm"

theorem ioccncflimc
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  let vx: setvar x
  let vk: setvar k
  assume ioccncflimc.a: |- ( ph -> A e. RR* )
  assume ioccncflimc.b: |- ( ph -> B e. RR )
  assume ioccncflimc.altb: |- ( ph -> A < B )
  assume ioccncflimc.f: |- ( ph -> F e. ( ( A (,] B ) -cn-> CC ) )


  assert |- ( ph -> ( F ` B ) e. ( ( F |` ( A (,) B ) ) limCC B ) )

  proof
    wph
    cB
    cF
    cfv
    cF
    cB
    climc
    co
    cF
    cA
    cB
    cioo
    co
    #
    cres
    cB
    climc
    co
    wph
    cA
    cB
    cioc
    co
    #
    cB
    cc
    cF
    ioccncflimc.f
    wph
    cA
    cB
    cB
    ioccncflimc.a
    wph
    cB
    ioccncflimc.b
    rexrd
    #
    @2
    ioccncflimc.altb
    wph
    cB
    ioccncflimc.b
    leidd
    eliocd
    #
    cnlimci
    wph
    @1
    cB
    @0
    cF
    ccnfld
    ctopn
    cfv
    #
    @1
    cB
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
    ioccncflimc.f
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
    ioccncflimc.f
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
    @16
    @20
    @4
    @18
    cnfldtopon
    @17
    @1
    @4
    cc
    resttopon
    sylancr
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
    ioossioc
    a1i
    @17
    @18
    @7
    eqid
    wph
    cB
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
    cB
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
    @25
    wph
    @30
    @1
    cB
    wph
    cB
    cc
    @30
    wph
    cB
    ioccncflimc.b
    recnd
    wph
    cc
    cc
    @29
    cfv
    #
    @30
    @22
    @32
    cc
    wceq
    @23
    @4
    cc
    unicntop
    ntrtop
    ax-mp
    wph
    cc
    @28
    @29
    wph
    @28
    cc
    wph
    @16
    @28
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
    @22
    @16
    @1
    @1
    wss
    #
    @25
    @31
    wceq
    @22
    wph
    @23
    a1i
    @17
    @33
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
    @26
    @24
    @27
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
    cB
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
    @26
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
    @26
    @1
    wceq
    ioccncflimc.a
    @2
    ioccncflimc.altb
    cA
    cB
    snunioo2
    syl3anc
    eqcomd
    fveq12d
    eleqtrd
    limcres
    eleqtrrd
end
