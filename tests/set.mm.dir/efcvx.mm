include "cr.mm"
include "wcel.mm"
include "clt.mm"
include "wbr.mm"
include "w3a.mm"
include "cc0.mm"
include "c1.mm"
include "cioo.mm"
include "co.mm"
include "wa.mm"
include "cmul.mm"
include "cmin.mm"
include "caddc.mm"
include "ce.mm"
include "cicc.mm"
include "cres.mm"
include "cfv.mm"
include "cima.mm"
include "simpl1.mm"
include "simpl2.mm"
include "simpl3.mm"
include "ccncf.mm"
include "wf.mm"
include "wss.mm"
include "crp.mm"
include "wf1o.mm"
include "reeff1o.mm"
include "f1of.mm"
include "ax-mp.mm"
include "rpssre.mm"
include "fss.mm"
include "mp2an.mm"
include "iccssre.mm"
include "syl2anc.mm"
include "fssres2.mm"
include "sylancr.mm"
include "cc.mm"
include "wb.mm"
include "ax-resscn.mm"
include "syl6ss.mm"
include "efcn.mm"
include "rescncf.mm"
include "mpisyl.mm"
include "cncffvrn.mm"
include "mpbird.mm"
include "cdv.mm"
include "wiso.mm"
include "wceq.mm"
include "reefiso.mm"
include "a1i.mm"
include "ioossre.mm"
include "eqidd.mm"
include "isores3.mm"
include "syl3anc.mm"
include "crn.mm"
include "ctg.mm"
include "cnt.mm"
include "ssid.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "eqid.mm"
include "tgioo2.mm"
include "dvres.mm"
include "mpanl12.mm"
include "resabs1d.mm"
include "oveq2d.mm"
include "cpr.mm"
include "cdm.mm"
include "reelprrecn.mm"
include "eff.mm"
include "dvef.mm"
include "dmeqi.mm"
include "fdmi.mm"
include "eqtri.mm"
include "sseqtr4i.mm"
include "dvres3.mm"
include "mp4an.mm"
include "reseq1i.mm"
include "iccntr.mm"
include "reseq12d.mm"
include "3eqtr3d.mm"
include "isoeq1.mm"
include "syl.mm"
include "simpr.mm"
include "dvcvx.mm"
include "ax-1cn.mm"
include "sseldi.mm"
include "recnd.mm"
include "nncan.mm"
include "oveq1d.mm"
include "ioossicc.mm"
include "iirev.mm"
include "lincmb01cmp.mm"
include "syldan.mm"
include "eqeltrrd.mm"
include "fvres.mm"
include "cxr.mm"
include "cle.mm"
include "rexrd.mm"
include "ltled.mm"
include "lbicc2.mm"
include "ubicc2.mm"
include "oveq12d.mm"
include "3brtr3d.mm"

theorem efcvx
  let cA: class A
  let cB: class B
  let cT: class T


  assert |- ( ( ( A e. RR /\ B e. RR /\ A < B ) /\ T e. ( 0 (,) 1 ) ) -> ( exp ` ( ( T x. A ) + ( ( 1 - T ) x. B ) ) ) < ( ( T x. ( exp ` A ) ) + ( ( 1 - T ) x. ( exp ` B ) ) ) )

  proof
    cA
    cr
    wcel
    #
    cB
    cr
    wcel
    #
    cA
    cB
    clt
    wbr
    #
    w3a
    #
    cT
    cc0
    c1
    cioo
    co
    #
    wcel
    #
    wa
    #
    cT
    cA
    cmul
    co
    #
    c1
    cT
    cmin
    co
    #
    cB
    cmul
    co
    #
    caddc
    co
    #
    ce
    cA
    cB
    cicc
    co
    #
    cres
    #
    cfv
    #
    cT
    cA
    @12
    cfv
    #
    cmul
    co
    #
    @8
    cB
    @12
    cfv
    #
    cmul
    co
    #
    caddc
    co
    @10
    ce
    cfv
    #
    cT
    cA
    ce
    cfv
    #
    cmul
    co
    #
    @8
    cB
    ce
    cfv
    #
    cmul
    co
    #
    caddc
    co
    clt
    @6
    cA
    cB
    @10
    cT
    @12
    ce
    cr
    cres
    #
    cA
    cB
    cioo
    co
    #
    cima
    #
    @0
    @1
    @2
    @5
    simpl1
    #
    @0
    @1
    @2
    @5
    simpl2
    #
    @0
    @1
    @2
    @5
    simpl3
    #
    @6
    @12
    @11
    cr
    ccncf
    co
    wcel
    #
    @11
    cr
    @12
    wf
    #
    @6
    cr
    cr
    @23
    wf
    #
    @11
    cr
    wss
    #
    @30
    cr
    crp
    @23
    wf
    #
    crp
    cr
    wss
    @31
    cr
    crp
    @23
    wf1o
    @33
    reeff1o
    cr
    crp
    @23
    f1of
    ax-mp
    rpssre
    cr
    crp
    cr
    @23
    fss
    mp2an
    #
    @6
    @0
    @1
    @32
    @26
    @27
    cA
    cB
    iccssre
    syl2anc
    #
    cr
    cr
    @11
    ce
    fssres2
    sylancr
    @6
    cr
    cc
    wss
    #
    @12
    @11
    cc
    ccncf
    co
    wcel
    #
    @29
    @30
    wb
    ax-resscn
    @6
    @11
    cc
    wss
    ce
    cc
    cc
    ccncf
    co
    wcel
    @37
    @6
    @11
    cr
    cc
    @35
    ax-resscn
    syl6ss
    efcn
    cc
    cc
    @11
    ce
    rescncf
    mpisyl
    @11
    cc
    cr
    @12
    cncffvrn
    sylancr
    mpbird
    @6
    @24
    @25
    clt
    clt
    cr
    @12
    cdv
    co
    #
    wiso
    #
    @24
    @25
    clt
    clt
    @23
    @24
    cres
    #
    wiso
    #
    @6
    cr
    crp
    clt
    clt
    @23
    wiso
    #
    @24
    cr
    wss
    #
    @25
    @25
    wceq
    @41
    @42
    @6
    reefiso
    a1i
    @43
    @6
    cA
    cB
    ioossre
    a1i
    @6
    @25
    eqidd
    cr
    crp
    clt
    clt
    @23
    @24
    @25
    isores3
    syl3anc
    @6
    @38
    @40
    wceq
    @39
    @41
    wb
    @6
    cr
    @23
    @11
    cres
    #
    cdv
    co
    #
    cr
    @23
    cdv
    co
    #
    @11
    cioo
    crn
    ctg
    cfv
    #
    cnt
    cfv
    cfv
    #
    cres
    #
    @38
    @40
    @6
    cr
    cr
    wss
    #
    @32
    @45
    @49
    wceq
    #
    cr
    ssid
    @35
    @36
    cr
    cc
    @23
    wf
    #
    @50
    @32
    wa
    @51
    ax-resscn
    @31
    @36
    @52
    @34
    ax-resscn
    cr
    cr
    cc
    @23
    fss
    mp2an
    cr
    @11
    cr
    @47
    @23
    ccnfld
    ctopn
    cfv
    #
    @53
    eqid
    #
    @53
    @54
    tgioo2
    dvres
    mpanl12
    sylancr
    @6
    @44
    @12
    cr
    cdv
    @6
    ce
    @11
    cr
    @35
    resabs1d
    oveq2d
    @6
    @46
    @23
    @48
    @24
    @46
    @23
    wceq
    @6
    @46
    cc
    ce
    cdv
    co
    #
    cr
    cres
    #
    @23
    cr
    cr
    cc
    cpr
    wcel
    cc
    cc
    ce
    wf
    cc
    cc
    wss
    cr
    @55
    cdm
    #
    wss
    @46
    @56
    wceq
    reelprrecn
    eff
    cc
    ssid
    cr
    cc
    @57
    ax-resscn
    @57
    ce
    cdm
    cc
    @55
    ce
    dvef
    dmeqi
    cc
    cc
    ce
    eff
    fdmi
    eqtri
    sseqtr4i
    cc
    cr
    ce
    dvres3
    mp4an
    @55
    ce
    cr
    dvef
    reseq1i
    eqtri
    a1i
    @6
    @0
    @1
    @48
    @24
    wceq
    @26
    @27
    cA
    cB
    iccntr
    syl2anc
    reseq12d
    3eqtr3d
    @24
    @25
    clt
    clt
    @40
    @38
    isoeq1
    syl
    mpbird
    @3
    @5
    simpr
    #
    @10
    eqid
    dvcvx
    @6
    @10
    @11
    wcel
    @13
    @18
    wceq
    @6
    c1
    @8
    cmin
    co
    #
    cA
    cmul
    co
    #
    @9
    caddc
    co
    #
    @10
    @11
    @6
    @60
    @7
    @9
    caddc
    @6
    @59
    cT
    cA
    cmul
    @6
    c1
    cc
    wcel
    cT
    cc
    wcel
    @59
    cT
    wceq
    ax-1cn
    @6
    cT
    @6
    @4
    cr
    cT
    cc0
    c1
    ioossre
    @58
    sseldi
    recnd
    c1
    cT
    nncan
    sylancr
    oveq1d
    oveq1d
    @3
    @5
    @8
    cc0
    c1
    cicc
    co
    #
    wcel
    #
    @61
    @11
    wcel
    @6
    cT
    @62
    wcel
    @63
    @6
    @4
    @62
    cT
    cc0
    c1
    ioossicc
    @58
    sseldi
    cT
    iirev
    syl
    cA
    cB
    @8
    lincmb01cmp
    syldan
    eqeltrrd
    @10
    @11
    ce
    fvres
    syl
    @6
    @15
    @20
    @17
    @22
    caddc
    @6
    @14
    @19
    cT
    cmul
    @6
    cA
    @11
    wcel
    #
    @14
    @19
    wceq
    @6
    cA
    cxr
    wcel
    #
    cB
    cxr
    wcel
    #
    cA
    cB
    cle
    wbr
    #
    @64
    @6
    cA
    @26
    rexrd
    #
    @6
    cB
    @27
    rexrd
    #
    @6
    cA
    cB
    @26
    @27
    @28
    ltled
    #
    cA
    cB
    lbicc2
    syl3anc
    cA
    @11
    ce
    fvres
    syl
    oveq2d
    @6
    @16
    @21
    @8
    cmul
    @6
    cB
    @11
    wcel
    #
    @16
    @21
    wceq
    @6
    @65
    @66
    @67
    @71
    @68
    @69
    @70
    cA
    cB
    ubicc2
    syl3anc
    cB
    @11
    ce
    fvres
    syl
    oveq2d
    oveq12d
    3brtr3d
end
