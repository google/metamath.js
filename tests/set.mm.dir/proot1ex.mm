include "cn.mm"
include "wcel.mm"
include "c1.mm"
include "cneg.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "ccxp.mm"
include "ccnv.mm"
include "csn.mm"
include "cima.mm"
include "cc.mm"
include "cc0.mm"
include "cdif.mm"
include "cfv.mm"
include "wceq.mm"
include "wne.mm"
include "neg1cn.mm"
include "crp.mm"
include "2rp.mm"
include "nnrp.mm"
include "rpdivcl.mm"
include "sylancr.mm"
include "rpcnd.mm"
include "cxpcl.mm"
include "a1i.mm"
include "neg1ne0.mm"
include "cxpne0d.mm"
include "eldifsn.mm"
include "sylanbrc.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "cmg.mm"
include "wb.mm"
include "cn0.mm"
include "wral.mm"
include "wa.mm"
include "cmul.mm"
include "cz.mm"
include "clog.mm"
include "ce.mm"
include "ci.mm"
include "cpi.mm"
include "nn0cn.mm"
include "mulcl.mm"
include "syl2an.mm"
include "cxpefd.mm"
include "eqeq1d.mm"
include "logcl.mm"
include "mp2an.mm"
include "sylancl.mm"
include "efeq1.mm"
include "syl.mm"
include "2cn.mm"
include "nncn.mm"
include "adantr.mm"
include "adantl.mm"
include "nnne0.mm"
include "div13d.mm"
include "logm1.mm"
include "oveq12d.mm"
include "divcld.mm"
include "ax-icn.mm"
include "picn.mm"
include "mulcli.mm"
include "mulassd.mm"
include "mul12d.mm"
include "oveq2d.mm"
include "3eqtrd.mm"
include "oveq1d.mm"
include "ine0.mm"
include "2ne0.mm"
include "pire.mm"
include "pipos.mm"
include "gt0ne0ii.mm"
include "mulne0i.mm"
include "divcan4d.mm"
include "eqtrd.mm"
include "eleq1d.mm"
include "3bitrd.mm"
include "cexp.mm"
include "ccnfld.mm"
include "cmgp.mm"
include "simpr.mm"
include "cxpmul2d.mm"
include "cnfldexp.mm"
include "sylan.mm"
include "csubmnd.mm"
include "crg.mm"
include "cnring.mm"
include "cnfldbas.mm"
include "cnfld0.mm"
include "cndrng.mm"
include "drngui.mm"
include "eqid.mm"
include "unitsubm.mm"
include "mp1i.mm"
include "submmulg.mm"
include "syl3anc.mm"
include "3eqtr2rd.mm"
include "nnz.mm"
include "nn0z.mm"
include "dvdsval2.mm"
include "3bitr4rd.mm"
include "ralrimiva.mm"
include "cgrp.mm"
include "unitgrp.mm"
include "nnnn0.mm"
include "unitgrpbas.mm"
include "c0g.mm"
include "cnfld1.mm"
include "unitgrpid.mm"
include "ax-mp.mm"
include "odeq.mm"
include "mpbird.mm"
include "eqcomd.mm"
include "wfn.mm"
include "wf.mm"
include "odf.mm"
include "ffn.mm"
include "fniniseg.mm"
include "mpbir2and.mm"

theorem proot1ex
  let cG: class G
  let cN: class N
  let cO: class O
  let vx: setvar x
  assume proot1ex.g: |- G = ( ( mulGrp ` CCfld ) |`s ( CC \ { 0 } ) )
  assume proot1ex.o: |- O = ( od ` G )


  assert |- ( N e. NN -> ( -u 1 ^c ( 2 / N ) ) e. ( `' O " { N } ) )

  proof
    cN
    cn
    wcel
    #
    c1
    cneg
    #
    c2
    cN
    cdiv
    co
    #
    ccxp
    co
    #
    cO
    ccnv
    cN
    csn
    cima
    wcel
    #
    @3
    cc
    cc0
    csn
    cdif
    #
    wcel
    #
    @3
    cO
    cfv
    #
    cN
    wceq
    #
    @0
    @3
    cc
    wcel
    #
    @3
    cc0
    wne
    @6
    @0
    @1
    cc
    wcel
    #
    @2
    cc
    wcel
    #
    @9
    neg1cn
    @0
    @2
    @0
    c2
    crp
    wcel
    cN
    crp
    wcel
    @2
    crp
    wcel
    2rp
    cN
    nnrp
    c2
    cN
    rpdivcl
    sylancr
    rpcnd
    #
    @1
    @2
    cxpcl
    sylancr
    #
    @0
    @1
    @2
    @10
    @0
    neg1cn
    a1i
    @1
    cc0
    wne
    #
    @0
    neg1ne0
    a1i
    @12
    cxpne0d
    @3
    cc
    cc0
    eldifsn
    sylanbrc
    #
    @0
    cN
    @7
    @0
    cN
    @7
    wceq
    #
    cN
    vx
    cv
    #
    cdvds
    wbr
    #
    @17
    @3
    cG
    cmg
    cfv
    #
    co
    #
    c1
    wceq
    #
    wb
    #
    vx
    cn0
    wral
    #
    @0
    @22
    vx
    cn0
    @0
    @17
    cn0
    wcel
    #
    wa
    #
    @1
    @2
    @17
    cmul
    co
    #
    ccxp
    co
    #
    c1
    wceq
    #
    @17
    cN
    cdiv
    co
    #
    cz
    wcel
    #
    @21
    @18
    @25
    @28
    @26
    @1
    clog
    cfv
    #
    cmul
    co
    #
    ce
    cfv
    #
    c1
    wceq
    #
    @32
    ci
    c2
    cpi
    cmul
    co
    #
    cmul
    co
    #
    cdiv
    co
    #
    cz
    wcel
    #
    @30
    @25
    @27
    @33
    c1
    @25
    @1
    @26
    @10
    @25
    neg1cn
    a1i
    #
    @14
    @25
    neg1ne0
    a1i
    @0
    @11
    @17
    cc
    wcel
    #
    @26
    cc
    wcel
    #
    @24
    @12
    @17
    nn0cn
    #
    @2
    @17
    mulcl
    syl2an
    #
    cxpefd
    eqeq1d
    @25
    @32
    cc
    wcel
    #
    @34
    @38
    wb
    @25
    @41
    @31
    cc
    wcel
    #
    @44
    @43
    @10
    @14
    @45
    neg1cn
    neg1ne0
    @1
    logcl
    mp2an
    @26
    @31
    mulcl
    sylancl
    @32
    efeq1
    syl
    @25
    @37
    @29
    cz
    @25
    @37
    @29
    @36
    cmul
    co
    #
    @36
    cdiv
    co
    @29
    @25
    @32
    @46
    @36
    cdiv
    @25
    @32
    @29
    c2
    cmul
    co
    #
    ci
    cpi
    cmul
    co
    #
    cmul
    co
    @29
    c2
    @48
    cmul
    co
    #
    cmul
    co
    @46
    @25
    @26
    @47
    @31
    @48
    cmul
    @25
    c2
    cN
    @17
    c2
    cc
    wcel
    @25
    2cn
    a1i
    #
    @0
    cN
    cc
    wcel
    @24
    cN
    nncn
    adantr
    #
    @24
    @40
    @0
    @42
    adantl
    #
    @0
    cN
    cc0
    wne
    #
    @24
    cN
    nnne0
    adantr
    #
    div13d
    @31
    @48
    wceq
    @25
    logm1
    a1i
    oveq12d
    @25
    @29
    c2
    @48
    @25
    @17
    cN
    @52
    @51
    @54
    divcld
    #
    @50
    @48
    cc
    wcel
    @25
    ci
    cpi
    ax-icn
    picn
    mulcli
    a1i
    mulassd
    @25
    @49
    @36
    @29
    cmul
    @25
    c2
    ci
    cpi
    @50
    ci
    cc
    wcel
    @25
    ax-icn
    a1i
    cpi
    cc
    wcel
    @25
    picn
    a1i
    mul12d
    oveq2d
    3eqtrd
    oveq1d
    @25
    @29
    @36
    @55
    @36
    cc
    wcel
    @25
    ci
    @35
    ax-icn
    c2
    cpi
    2cn
    picn
    mulcli
    #
    mulcli
    a1i
    @36
    cc0
    wne
    @25
    ci
    @35
    ax-icn
    @56
    ine0
    c2
    cpi
    2cn
    picn
    2ne0
    cpi
    pire
    pipos
    gt0ne0ii
    mulne0i
    mulne0i
    a1i
    divcan4d
    eqtrd
    eleq1d
    3bitrd
    @25
    @20
    @27
    c1
    @25
    @27
    @3
    @17
    cexp
    co
    #
    @17
    @3
    ccnfld
    cmgp
    cfv
    #
    cmg
    cfv
    #
    co
    #
    @20
    @25
    @1
    @2
    @17
    @39
    @0
    @11
    @24
    @12
    adantr
    @0
    @24
    simpr
    #
    cxpmul2d
    @0
    @9
    @24
    @60
    @57
    wceq
    @13
    @3
    @17
    cnfldexp
    sylan
    @25
    @5
    @58
    csubmnd
    cfv
    wcel
    #
    @24
    @6
    @60
    @20
    wceq
    ccnfld
    crg
    wcel
    #
    @62
    @25
    cnring
    ccnfld
    @5
    @58
    cc
    ccnfld
    cc0
    cnfldbas
    cnfld0
    cndrng
    drngui
    #
    @58
    eqid
    unitsubm
    mp1i
    @61
    @0
    @6
    @24
    @15
    adantr
    @5
    @59
    @19
    @58
    cG
    @17
    @3
    @59
    eqid
    proot1ex.g
    @19
    eqid
    #
    submmulg
    syl3anc
    3eqtr2rd
    eqeq1d
    @25
    cN
    cz
    wcel
    #
    @53
    @17
    cz
    wcel
    #
    @18
    @30
    wb
    @0
    @66
    @24
    cN
    nnz
    adantr
    @54
    @24
    @67
    @0
    @17
    nn0z
    adantl
    cN
    @17
    dvdsval2
    syl3anc
    3bitr4rd
    ralrimiva
    @0
    cG
    cgrp
    wcel
    #
    @6
    cN
    cn0
    wcel
    @16
    @23
    wb
    @63
    @68
    @0
    cnring
    ccnfld
    @5
    cG
    @64
    proot1ex.g
    unitgrp
    mp1i
    @15
    cN
    nnnn0
    vx
    @3
    @19
    cG
    cN
    cO
    @5
    c1
    ccnfld
    @5
    cG
    @64
    proot1ex.g
    unitgrpbas
    #
    proot1ex.o
    @65
    @63
    c1
    cG
    c0g
    cfv
    wceq
    cnring
    ccnfld
    @5
    c1
    cG
    @64
    proot1ex.g
    cnfld1
    unitgrpid
    ax-mp
    odeq
    syl3anc
    mpbird
    eqcomd
    cO
    @5
    wfn
    #
    @4
    @6
    @8
    wa
    wb
    @0
    @5
    cn0
    cO
    wf
    @70
    cG
    cO
    @5
    @69
    proot1ex.o
    odf
    @5
    cn0
    cO
    ffn
    ax-mp
    @5
    cN
    @3
    cO
    fniniseg
    mp1i
    mpbir2and
end
