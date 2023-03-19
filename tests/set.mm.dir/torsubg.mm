include "cabl.mm"
include "wcel.mm"
include "ccnv.mm"
include "cn.mm"
include "cima.mm"
include "csubg.mm"
include "cfv.mm"
include "cbs.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "cv.mm"
include "cplusg.mm"
include "co.mm"
include "wral.mm"
include "cminusg.mm"
include "wa.mm"
include "cdm.mm"
include "cnvimass.mm"
include "cn0.mm"
include "eqid.mm"
include "odf.mm"
include "fdmi.mm"
include "sseqtri.mm"
include "a1i.mm"
include "c0g.mm"
include "cgrp.mm"
include "ablgrp.mm"
include "grpidcl.mm"
include "syl.mm"
include "c1.mm"
include "wceq.mm"
include "od1.mm"
include "1nn.mm"
include "syl6eqel.mm"
include "wfn.mm"
include "wb.mm"
include "wf.mm"
include "ffn.mm"
include "ax-mp.mm"
include "elpreima.mm"
include "sylanbrc.mm"
include "ne0i.mm"
include "ad2antrr.mm"
include "sseli.mm"
include "ad2antlr.mm"
include "adantl.mm"
include "grpcl.mm"
include "syl3anc.mm"
include "cc0.mm"
include "cgcd.mm"
include "cmul.mm"
include "cdvds.mm"
include "wbr.mm"
include "0nnn.mm"
include "odcl.mm"
include "nn0zd.mm"
include "gcdcld.mm"
include "nn0cnd.mm"
include "mul02d.mm"
include "breq1d.mm"
include "cz.mm"
include "zmulcld.mm"
include "0dvds.mm"
include "bitrd.mm"
include "simprbi.mm"
include "nnmulcld.mm"
include "eleq1.mm"
include "syl5ibcom.mm"
include "sylbid.mm"
include "mtoi.mm"
include "simpll.mm"
include "odadd1.mm"
include "oveq1.mm"
include "mtod.mm"
include "wo.mm"
include "elnn0.mm"
include "sylib.mm"
include "ord.mm"
include "mt3d.mm"
include "ralrimiva.mm"
include "grpinvcl.mm"
include "syl2an.mm"
include "odinv.mm"
include "eqeltrd.mm"
include "jca.mm"
include "w3a.mm"
include "issubg2.mm"
include "mpbir3and.mm"

theorem torsubg
  let cG: class G
  let cO: class O
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cN: class N
  assume torsubg.1: |- O = ( od ` G )


  assert |- ( G e. Abel -> ( `' O " NN ) e. ( SubGrp ` G ) )

  proof
    cG
    cabl
    wcel
    #
    cO
    ccnv
    cn
    cima
    #
    cG
    csubg
    cfv
    wcel
    #
    @1
    cG
    cbs
    cfv
    #
    wss
    #
    @1
    c0
    wne
    #
    vx
    cv
    #
    vy
    cv
    #
    cG
    cplusg
    cfv
    #
    co
    #
    @1
    wcel
    #
    vy
    @1
    wral
    #
    @6
    cG
    cminusg
    cfv
    #
    cfv
    #
    @1
    wcel
    #
    wa
    #
    vx
    @1
    wral
    #
    @4
    @0
    @1
    cO
    cdm
    @3
    cO
    cn
    cnvimass
    @3
    cn0
    cO
    cG
    cO
    @3
    @3
    eqid
    #
    torsubg.1
    odf
    #
    fdmi
    sseqtri
    #
    a1i
    @0
    cG
    c0g
    cfv
    #
    @1
    wcel
    #
    @5
    @0
    @20
    @3
    wcel
    #
    @20
    cO
    cfv
    #
    cn
    wcel
    #
    @21
    @0
    cG
    cgrp
    wcel
    #
    @22
    cG
    ablgrp
    #
    @3
    cG
    @20
    @17
    @20
    eqid
    #
    grpidcl
    syl
    @0
    @23
    c1
    cn
    @0
    @25
    @23
    c1
    wceq
    @26
    cG
    cO
    @20
    torsubg.1
    @27
    od1
    syl
    1nn
    syl6eqel
    cO
    @3
    wfn
    #
    @21
    @22
    @24
    wa
    wb
    @3
    cn0
    cO
    wf
    @28
    @18
    @3
    cn0
    cO
    ffn
    ax-mp
    #
    @3
    @20
    cn
    cO
    elpreima
    ax-mp
    sylanbrc
    @1
    @20
    ne0i
    syl
    @0
    @15
    vx
    @1
    @0
    @6
    @1
    wcel
    #
    wa
    #
    @11
    @14
    @31
    @10
    vy
    @1
    @31
    @7
    @1
    wcel
    #
    wa
    #
    @9
    @3
    wcel
    #
    @9
    cO
    cfv
    #
    cn
    wcel
    #
    @10
    @33
    @25
    @6
    @3
    wcel
    #
    @7
    @3
    wcel
    #
    @34
    @0
    @25
    @30
    @32
    @26
    ad2antrr
    @30
    @37
    @0
    @32
    @1
    @3
    @6
    @19
    sseli
    #
    ad2antlr
    #
    @32
    @38
    @31
    @1
    @3
    @7
    @19
    sseli
    adantl
    #
    @3
    @8
    cG
    @6
    @7
    @17
    @8
    eqid
    #
    grpcl
    syl3anc
    #
    @33
    @36
    @35
    cc0
    wceq
    #
    @33
    @44
    cc0
    @6
    cO
    cfv
    #
    @7
    cO
    cfv
    #
    cgcd
    co
    #
    cmul
    co
    #
    @45
    @46
    cmul
    co
    #
    cdvds
    wbr
    #
    @33
    @50
    cc0
    cn
    wcel
    #
    0nnn
    @33
    @50
    @49
    cc0
    wceq
    #
    @51
    @33
    @50
    cc0
    @49
    cdvds
    wbr
    #
    @52
    @33
    @48
    cc0
    @49
    cdvds
    @33
    @47
    @33
    @47
    @33
    @45
    @46
    @33
    @45
    @33
    @37
    @45
    cn0
    wcel
    @40
    @6
    cG
    cO
    @3
    @17
    torsubg.1
    odcl
    syl
    nn0zd
    #
    @33
    @46
    @33
    @38
    @46
    cn0
    wcel
    @41
    @7
    cG
    cO
    @3
    @17
    torsubg.1
    odcl
    syl
    nn0zd
    #
    gcdcld
    nn0cnd
    mul02d
    breq1d
    @33
    @49
    cz
    wcel
    @53
    @52
    wb
    @33
    @45
    @46
    @54
    @55
    zmulcld
    @49
    0dvds
    syl
    bitrd
    @33
    @49
    cn
    wcel
    @52
    @51
    @33
    @45
    @46
    @30
    @45
    cn
    wcel
    #
    @0
    @32
    @30
    @37
    @56
    @28
    @30
    @37
    @56
    wa
    wb
    @29
    @3
    @6
    cn
    cO
    elpreima
    ax-mp
    simprbi
    #
    ad2antlr
    @32
    @46
    cn
    wcel
    #
    @31
    @32
    @38
    @58
    @28
    @32
    @38
    @58
    wa
    wb
    @29
    @3
    @7
    cn
    cO
    elpreima
    ax-mp
    simprbi
    adantl
    nnmulcld
    @49
    cc0
    cn
    eleq1
    syl5ibcom
    sylbid
    mtoi
    @33
    @35
    @47
    cmul
    co
    #
    @49
    cdvds
    wbr
    #
    @44
    @50
    @33
    @0
    @37
    @38
    @60
    @0
    @30
    @32
    simpll
    @40
    @41
    @6
    @7
    @8
    cG
    cO
    @3
    torsubg.1
    @17
    @42
    odadd1
    syl3anc
    @44
    @59
    @48
    @49
    cdvds
    @35
    cc0
    @47
    cmul
    oveq1
    breq1d
    syl5ibcom
    mtod
    @33
    @36
    @44
    @33
    @35
    cn0
    wcel
    #
    @36
    @44
    wo
    @33
    @34
    @61
    @43
    @9
    cG
    cO
    @3
    @17
    torsubg.1
    odcl
    syl
    @35
    elnn0
    sylib
    ord
    mt3d
    @28
    @10
    @34
    @36
    wa
    wb
    @29
    @3
    @9
    cn
    cO
    elpreima
    ax-mp
    sylanbrc
    ralrimiva
    @31
    @13
    @3
    wcel
    #
    @13
    cO
    cfv
    #
    cn
    wcel
    #
    @14
    @0
    @25
    @37
    @62
    @30
    @26
    @39
    @3
    cG
    @12
    @6
    @17
    @12
    eqid
    #
    grpinvcl
    syl2an
    @31
    @63
    @45
    cn
    @0
    @25
    @37
    @63
    @45
    wceq
    @30
    @26
    @39
    @6
    cG
    @12
    cO
    @3
    torsubg.1
    @65
    @17
    odinv
    syl2an
    @30
    @56
    @0
    @57
    adantl
    eqeltrd
    @28
    @14
    @62
    @64
    wa
    wb
    @29
    @3
    @13
    cn
    cO
    elpreima
    ax-mp
    sylanbrc
    jca
    ralrimiva
    @0
    @25
    @2
    @4
    @5
    @16
    w3a
    wb
    @26
    vx
    vy
    @3
    @8
    @1
    cG
    @12
    @17
    @42
    @65
    issubg2
    syl
    mpbir3and
end
