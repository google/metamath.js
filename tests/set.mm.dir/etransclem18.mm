include "cioo.mm"
include "co.mm"
include "cicc.mm"
include "ceu.mm"
include "cv.mm"
include "cneg.mm"
include "ccxp.mm"
include "cfv.mm"
include "cmul.mm"
include "cc.mm"
include "wss.mm"
include "ioossicc.mm"
include "a1i.mm"
include "cvol.mm"
include "cdm.mm"
include "wcel.mm"
include "ioombl.mm"
include "wa.mm"
include "ere.mm"
include "recni.mm"
include "cr.mm"
include "iccssred.mm"
include "sselda.mm"
include "recnd.mm"
include "negcld.mm"
include "cxpcld.mm"
include "wf.mm"
include "dvdmsscn.mm"
include "etransclem8.mm"
include "adantr.mm"
include "ffvelrnd.mm"
include "mulcld.mm"
include "cmpt.mm"
include "ccncf.mm"
include "cibl.mm"
include "eqidd.mm"
include "wceq.mm"
include "oveq2.mm"
include "adantl.mm"
include "sstrd.mm"
include "negcl.mm"
include "syl.mm"
include "fvmptd.mm"
include "eqcomd.mm"
include "mpteq2dva.mm"
include "cmnf.mm"
include "cc0.mm"
include "cioc.mm"
include "cdif.mm"
include "wn.mm"
include "crp.mm"
include "epr.mm"
include "cxr.mm"
include "mnfxr.mm"
include "0red.mm"
include "rpxr.mm"
include "rpgt0.mm"
include "gtnelioc.mm"
include "ax-mp.mm"
include "eldif.mm"
include "mpbir2an.mm"
include "cxpcncf2.mm"
include "mp1i.mm"
include "eqid.mm"
include "negcncf.mm"
include "cncfmpt1f.mm"
include "eqeltrd.mm"
include "cfz.mm"
include "cmin.mm"
include "c1.mm"
include "cif.mm"
include "cexp.mm"
include "cprod.mm"
include "ax-resscn.mm"
include "cn.mm"
include "cn0.mm"
include "etransclem6.mm"
include "eqtri.mm"
include "etransclem13.mm"
include "fzfid.mm"
include "w3a.mm"
include "3adant3.mm"
include "elfzelz.mm"
include "zcnd.mm"
include "3ad2ant3.mm"
include "subcld.mm"
include "nnm1nn0.mm"
include "nnnn0d.mm"
include "ifcld.mm"
include "3ad2ant1.mm"
include "expcld.mm"
include "nfv.mm"
include "ssid.mm"
include "idcncfg.mm"
include "constcncfg.mm"
include "subcncf.mm"
include "expcncf.mm"
include "oveq1.mm"
include "cncfcompt2.mm"
include "fprodcncf.mm"
include "mulcncf.mm"
include "cniccibl.mm"
include "syl3anc.mm"
include "iblss.mm"

theorem etransclem18
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cP: class P
  let vj: setvar j
  let cF: class F
  let cM: class M
  let vk: setvar k
  let vy: setvar y
  assume etransclem18.s: |- ( ph -> RR e. { RR , CC } )
  assume etransclem18.x: |- ( ph -> RR e. ( ( TopOpen ` CCfld ) |`t RR ) )
  assume etransclem18.p: |- ( ph -> P e. NN )
  assume etransclem18.m: |- ( ph -> M e. NN0 )
  assume etransclem18.f: |- F = ( x e. RR |-> ( ( x ^ ( P - 1 ) ) x. prod_ j e. ( 1 ... M ) ( ( x - j ) ^ P ) ) )
  assume etransclem18.a: |- ( ph -> A e. RR )
  assume etransclem18.b: |- ( ph -> B e. RR )

  disjoint A x
  disjoint B x
  disjoint M j
  disjoint M x
  disjoint j x
  disjoint P j
  disjoint P x
  disjoint j ph
  disjoint ph x
  disjoint A k
  disjoint A y
  disjoint k x
  disjoint k y
  disjoint x y
  disjoint B k
  disjoint B y
  disjoint M k
  disjoint M y
  disjoint j k
  disjoint j y
  disjoint P k
  disjoint P y
  disjoint k ph
  disjoint ph y
  disjoint k x
  assert |- ( ph -> ( x e. ( A (,) B ) |-> ( ( _e ^c -u x ) x. ( F ` x ) ) ) e. L^1 )

  proof
    wph
    vx
    cA
    cB
    cioo
    co
    #
    cA
    cB
    cicc
    co
    #
    ceu
    vx
    cv
    #
    cneg
    #
    ccxp
    co
    #
    @2
    cF
    cfv
    #
    cmul
    co
    #
    cc
    @0
    @1
    wss
    wph
    cA
    cB
    ioossicc
    a1i
    @0
    cvol
    cdm
    wcel
    wph
    cA
    cB
    ioombl
    a1i
    wph
    @2
    @1
    wcel
    #
    wa
    #
    @4
    @5
    @8
    ceu
    @3
    ceu
    cc
    wcel
    #
    @8
    ceu
    ere
    recni
    #
    a1i
    @8
    @2
    @8
    @2
    wph
    @1
    cr
    @2
    wph
    cA
    cB
    etransclem18.a
    etransclem18.b
    iccssred
    #
    sselda
    #
    recnd
    #
    negcld
    cxpcld
    @8
    cr
    cc
    @2
    cF
    wph
    cr
    cc
    cF
    wf
    @7
    wph
    vx
    cP
    vj
    cF
    cM
    cr
    wph
    cr
    cr
    etransclem18.s
    etransclem18.x
    dvdmsscn
    #
    etransclem18.p
    etransclem18.f
    etransclem8
    adantr
    @12
    ffvelrnd
    mulcld
    wph
    cA
    cr
    wcel
    cB
    cr
    wcel
    vx
    @1
    @6
    cmpt
    #
    @1
    cc
    ccncf
    co
    #
    wcel
    @15
    cibl
    wcel
    etransclem18.a
    etransclem18.b
    wph
    vx
    @4
    @5
    @1
    wph
    vx
    @1
    @4
    cmpt
    vx
    @1
    @3
    vy
    cc
    ceu
    vy
    cv
    #
    ccxp
    co
    #
    cmpt
    #
    cfv
    #
    cmpt
    @16
    wph
    vx
    @1
    @4
    @20
    @8
    @20
    @4
    @8
    vy
    @3
    @18
    @4
    cc
    @19
    cc
    @8
    @19
    eqidd
    @17
    @3
    wceq
    @18
    @4
    wceq
    @8
    @17
    @3
    ceu
    ccxp
    oveq2
    adantl
    @8
    @2
    wph
    @1
    cc
    @2
    wph
    @1
    cr
    cc
    @11
    @14
    sstrd
    #
    sselda
    #
    negcld
    @8
    @2
    cc
    wcel
    #
    @4
    cc
    wcel
    @22
    @23
    ceu
    @3
    @9
    @23
    @10
    a1i
    @2
    negcl
    cxpcld
    syl
    fvmptd
    eqcomd
    mpteq2dva
    wph
    vx
    @3
    @19
    @1
    ceu
    cc
    cmnf
    cc0
    cioc
    co
    #
    cdif
    wcel
    #
    @19
    cc
    cc
    ccncf
    co
    #
    wcel
    wph
    @25
    @9
    ceu
    @24
    wcel
    wn
    #
    @10
    ceu
    crp
    wcel
    #
    @27
    epr
    @28
    cmnf
    cc0
    ceu
    cmnf
    cxr
    wcel
    @28
    mnfxr
    a1i
    @28
    0red
    ceu
    rpxr
    ceu
    rpgt0
    gtnelioc
    ax-mp
    ceu
    cc
    @24
    eldif
    mpbir2an
    vy
    ceu
    cxpcncf2
    mp1i
    wph
    @1
    cc
    wss
    #
    vx
    @1
    @3
    cmpt
    #
    @16
    wcel
    @21
    vx
    @1
    @30
    @30
    eqid
    negcncf
    syl
    cncfmpt1f
    eqeltrd
    wph
    vx
    @1
    @5
    cmpt
    vx
    @1
    cc0
    cM
    cfz
    co
    #
    @2
    vk
    cv
    #
    cmin
    co
    #
    @32
    cc0
    wceq
    #
    cP
    c1
    cmin
    co
    #
    cP
    cif
    #
    cexp
    co
    #
    vk
    cprod
    #
    cmpt
    @16
    wph
    vx
    @1
    @5
    @38
    @8
    vy
    cP
    vk
    cF
    cM
    cr
    @2
    cr
    cc
    wss
    @8
    ax-resscn
    a1i
    wph
    cP
    cn
    wcel
    #
    @7
    etransclem18.p
    adantr
    wph
    cM
    cn0
    wcel
    @7
    etransclem18.m
    adantr
    cF
    vx
    cr
    @2
    @35
    cexp
    co
    c1
    cM
    cfz
    co
    #
    @2
    vj
    cv
    cmin
    co
    cP
    cexp
    co
    vj
    cprod
    cmul
    co
    cmpt
    vy
    cr
    @17
    @35
    cexp
    co
    @40
    @17
    @32
    cmin
    co
    cP
    cexp
    co
    vk
    cprod
    cmul
    co
    cmpt
    etransclem18.f
    vx
    vy
    cP
    vj
    vk
    cM
    etransclem6
    eqtri
    @12
    etransclem13
    mpteq2dva
    wph
    vx
    @1
    @31
    @37
    vk
    @21
    wph
    cc0
    cM
    fzfid
    wph
    @7
    @32
    @31
    wcel
    #
    w3a
    #
    @33
    @36
    @42
    @2
    @32
    wph
    @7
    @23
    @41
    @13
    3adant3
    @41
    wph
    @32
    cc
    wcel
    #
    @7
    @41
    @32
    @32
    cc0
    cM
    elfzelz
    zcnd
    #
    3ad2ant3
    subcld
    wph
    @7
    @36
    cn0
    wcel
    #
    @41
    wph
    @34
    @35
    cP
    cn0
    wph
    @39
    @35
    cn0
    wcel
    etransclem18.p
    cP
    nnm1nn0
    syl
    wph
    cP
    etransclem18.p
    nnnn0d
    ifcld
    #
    3ad2ant1
    expcld
    wph
    @41
    wa
    #
    vx
    vy
    @1
    cc
    cc
    @33
    @17
    @36
    cexp
    co
    #
    @37
    cc
    @47
    vx
    nfv
    @47
    vx
    @2
    @32
    @1
    wph
    vx
    @1
    @2
    cmpt
    @16
    wcel
    @41
    wph
    vx
    @1
    cc
    @21
    cc
    cc
    wss
    #
    wph
    cc
    ssid
    #
    a1i
    idcncfg
    adantr
    @47
    vx
    @1
    @32
    cc
    wph
    @29
    @41
    @21
    adantr
    @41
    @43
    wph
    @44
    adantl
    @49
    @47
    @50
    a1i
    #
    constcncfg
    subcncf
    wph
    vy
    cc
    @48
    cmpt
    @26
    wcel
    #
    @41
    wph
    @45
    @52
    @46
    vy
    @36
    expcncf
    syl
    adantr
    @51
    @17
    @33
    @36
    cexp
    oveq1
    cncfcompt2
    fprodcncf
    eqeltrd
    mulcncf
    cA
    cB
    @15
    cniccibl
    syl3anc
    iblss
end
