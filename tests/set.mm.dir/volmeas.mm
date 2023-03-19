include "cvol.mm"
include "cdm.mm"
include "cmeas.mm"
include "cfv.mm"
include "wcel.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wf.mm"
include "c0.mm"
include "wceq.mm"
include "cv.mm"
include "com.mm"
include "cdom.mm"
include "wbr.mm"
include "wdisj.mm"
include "wa.mm"
include "cuni.mm"
include "cesum.mm"
include "wi.mm"
include "cpw.mm"
include "wral.mm"
include "volf.mm"
include "covol.mm"
include "csiga.mm"
include "crn.mm"
include "cr.mm"
include "fvssunirn.mm"
include "dmvlsiga.mm"
include "sselii.mm"
include "0elsiga.mm"
include "ax-mp.mm"
include "mblvol.mm"
include "ovol0.mm"
include "eqtri.mm"
include "cfn.mm"
include "cn.mm"
include "cen.mm"
include "simpr.mm"
include "nfv.mm"
include "nfdisj1.mm"
include "nfan.mm"
include "wss.mm"
include "elpwi.mm"
include "ad3antrrr.mm"
include "sseldd.mm"
include "ex.mm"
include "ralrimi.mm"
include "simplrr.mm"
include "w3a.mm"
include "ciun.mm"
include "uniiun.mm"
include "fveq2i.mm"
include "volfiniune.mm"
include "syl5eq.mm"
include "syl3anc.mm"
include "wf1o.mm"
include "wex.mm"
include "bren.mm"
include "nfcv.mm"
include "fveq2.mm"
include "simpl.mm"
include "eqidd.mm"
include "a1i.mm"
include "syl.mm"
include "sselda.mm"
include "ffvelrnd.mm"
include "esumf1o.mm"
include "adantlr.mm"
include "f1of.mm"
include "adantl.mm"
include "ffvelrnda.mm"
include "ralrimiva.mm"
include "id.mm"
include "disjrdx.mm"
include "biimpar.mm"
include "syl2anc.mm"
include "voliune.mm"
include "f1ofo.mm"
include "iunrdx.mm"
include "syl6eqr.mm"
include "fveq2d.mm"
include "3eqtr2rd.mm"
include "exlimdv.mm"
include "imp.mm"
include "sylan2b.mm"
include "wo.mm"
include "csdm.mm"
include "brdom2.mm"
include "biimpi.mm"
include "isfinite2.mm"
include "ensymb.mm"
include "nnenom.mm"
include "entr.mm"
include "mpan.mm"
include "sylbi.mm"
include "orim12i.mm"
include "ad2antrl.mm"
include "mpjaodan.mm"
include "rgen.mm"
include "wb.mm"
include "ismeas.mm"
include "mpbir3an.mm"

theorem volmeas
  let vf: setvar f
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y


  assert |- vol e. ( measures ` dom vol )

  proof
    cvol
    cvol
    cdm
    #
    cmeas
    cfv
    wcel
    #
    @0
    cc0
    cpnf
    cicc
    co
    #
    cvol
    wf
    #
    c0
    cvol
    cfv
    #
    cc0
    wceq
    #
    vx
    cv
    #
    com
    cdom
    wbr
    #
    vy
    @6
    vy
    cv
    #
    wdisj
    #
    wa
    #
    @6
    cuni
    #
    cvol
    cfv
    #
    @6
    @8
    cvol
    cfv
    #
    vy
    cesum
    #
    wceq
    #
    wi
    #
    vx
    @0
    cpw
    #
    wral
    #
    volf
    @4
    c0
    covol
    cfv
    #
    cc0
    c0
    @0
    wcel
    #
    @4
    @19
    wceq
    @0
    csiga
    crn
    cuni
    #
    wcel
    #
    @20
    cr
    csiga
    cfv
    @21
    @0
    csiga
    cr
    fvssunirn
    dmvlsiga
    sselii
    #
    @0
    0elsiga
    ax-mp
    c0
    mblvol
    ax-mp
    ovol0
    eqtri
    @16
    vx
    @17
    @6
    @17
    wcel
    #
    @10
    @15
    @24
    @10
    wa
    #
    @6
    cfn
    wcel
    #
    @15
    cn
    @6
    cen
    wbr
    #
    @25
    @26
    wa
    #
    @26
    @8
    @0
    wcel
    #
    vy
    @6
    wral
    #
    @9
    @15
    @25
    @26
    simpr
    @28
    @29
    vy
    @6
    @25
    @26
    vy
    @24
    @10
    vy
    @24
    vy
    nfv
    @7
    @9
    vy
    @7
    vy
    nfv
    vy
    @6
    @8
    nfdisj1
    nfan
    nfan
    @26
    vy
    nfv
    nfan
    @28
    @8
    @6
    wcel
    #
    @29
    @28
    @31
    wa
    @6
    @0
    @8
    @24
    @6
    @0
    wss
    #
    @10
    @26
    @31
    @6
    @0
    elpwi
    #
    ad3antrrr
    @28
    @31
    simpr
    sseldd
    ex
    ralrimi
    @24
    @7
    @9
    @26
    simplrr
    @26
    @30
    @9
    w3a
    @12
    vy
    @6
    @8
    ciun
    #
    cvol
    cfv
    @14
    @11
    @34
    cvol
    vy
    @6
    uniiun
    #
    fveq2i
    @6
    @8
    vy
    volfiniune
    syl5eq
    syl3anc
    @27
    @25
    cn
    @6
    vf
    cv
    #
    wf1o
    #
    vf
    wex
    #
    @15
    cn
    @6
    vf
    bren
    @25
    @38
    @15
    @25
    @37
    @15
    vf
    @25
    @37
    @15
    @25
    @37
    wa
    #
    @14
    cn
    vn
    cv
    #
    @36
    cfv
    #
    cvol
    cfv
    #
    vn
    cesum
    #
    vn
    cn
    @41
    ciun
    #
    cvol
    cfv
    #
    @12
    @24
    @37
    @14
    @43
    wceq
    @10
    @24
    @37
    wa
    #
    @6
    @13
    cn
    @42
    vy
    vn
    @36
    @41
    @17
    @46
    vn
    nfv
    vn
    @13
    nfcv
    vy
    @42
    nfcv
    vn
    @6
    nfcv
    vn
    cn
    nfcv
    vn
    @36
    nfcv
    @8
    @41
    cvol
    fveq2
    @24
    @37
    simpl
    #
    @24
    @37
    simpr
    @46
    @40
    cn
    wcel
    #
    wa
    @41
    eqidd
    @46
    @31
    wa
    #
    @0
    @2
    @8
    cvol
    @3
    @49
    volf
    a1i
    @46
    @6
    @0
    @8
    @46
    @24
    @32
    @47
    @33
    syl
    sselda
    ffvelrnd
    esumf1o
    adantlr
    @39
    @41
    @0
    wcel
    #
    vn
    cn
    wral
    vn
    cn
    @41
    wdisj
    #
    @45
    @43
    wceq
    @39
    @50
    vn
    cn
    @39
    @48
    wa
    @6
    @0
    @41
    @24
    @32
    @10
    @37
    @48
    @33
    ad3antrrr
    @39
    cn
    @6
    @40
    @36
    @37
    cn
    @6
    @36
    wf
    @25
    cn
    @6
    @36
    f1of
    adantl
    ffvelrnda
    sseldd
    ralrimiva
    @39
    @37
    @9
    @51
    @25
    @37
    simpr
    @24
    @7
    @9
    @37
    simplrr
    @37
    @51
    @9
    @37
    vn
    vy
    cn
    @41
    @6
    @8
    @36
    @37
    id
    @37
    @8
    @41
    wceq
    simpr
    #
    disjrdx
    biimpar
    syl2anc
    @41
    vn
    voliune
    syl2anc
    @37
    @45
    @12
    wceq
    @25
    @37
    @44
    @11
    cvol
    @37
    @44
    @34
    @11
    @37
    vn
    vy
    cn
    @41
    @6
    @8
    @36
    cn
    @6
    @36
    f1ofo
    @52
    iunrdx
    @35
    syl6eqr
    fveq2d
    adantl
    3eqtr2rd
    ex
    exlimdv
    imp
    sylan2b
    @7
    @26
    @27
    wo
    #
    @24
    @9
    @7
    @6
    com
    csdm
    wbr
    #
    @6
    com
    cen
    wbr
    #
    wo
    #
    @53
    @7
    @56
    @6
    com
    brdom2
    biimpi
    @54
    @26
    @55
    @27
    @6
    isfinite2
    @55
    com
    @6
    cen
    wbr
    #
    @27
    @6
    com
    ensymb
    cn
    com
    cen
    wbr
    @57
    @27
    nnenom
    cn
    com
    @6
    entr
    mpan
    sylbi
    orim12i
    syl
    ad2antrl
    mpjaodan
    ex
    rgen
    @22
    @1
    @3
    @5
    @18
    w3a
    wb
    @23
    vx
    vy
    @0
    cvol
    ismeas
    ax-mp
    mpbir3an
end
