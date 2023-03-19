include "cn.mm"
include "wcel.mm"
include "cv.mm"
include "czrh.mm"
include "cfv.mm"
include "wceq.mm"
include "cz.mm"
include "wrex.mm"
include "cbs.mm"
include "wfo.mm"
include "cn0.mm"
include "nnnn0.mm"
include "eqid.mm"
include "znzrhfo.mm"
include "syl.mm"
include "rrgss.mm"
include "sseli.mm"
include "foelrn.mm"
include "syl2an.mm"
include "ex.mm"
include "wi.mm"
include "wa.mm"
include "cgcd.mm"
include "co.mm"
include "c1.mm"
include "cdvds.mm"
include "wbr.mm"
include "cdiv.mm"
include "cmul.mm"
include "cc.mm"
include "nncn.mm"
include "ad2antrr.mm"
include "cc0.mm"
include "wn.mm"
include "simplr.mm"
include "nnz.mm"
include "wne.mm"
include "nnne0.mm"
include "simpr.mm"
include "necon3ai.mm"
include "gcdn0cl.mm"
include "syl21anc.mm"
include "nncnd.mm"
include "nnne0d.mm"
include "divcan2d.mm"
include "gcddvds.mm"
include "syl2anc.mm"
include "simpld.mm"
include "nnzd.mm"
include "simprd.mm"
include "wb.mm"
include "simpll.mm"
include "nndivdvds.mm"
include "mpbid.mm"
include "dvdsmulc.mm"
include "syl3anc.mm"
include "mpd.mm"
include "eqbrtrrd.mm"
include "cmulr.mm"
include "c0g.mm"
include "wf.mm"
include "fof.mm"
include "ffvelrnd.mm"
include "rrgeq0i.mm"
include "zring.mm"
include "crh.mm"
include "crg.mm"
include "ccrg.mm"
include "zncrng.mm"
include "crngring.mm"
include "zrhrhm.mm"
include "zringbas.mm"
include "zringmulr.mm"
include "rhmmul.mm"
include "eqeq1d.mm"
include "zmulcld.mm"
include "zndvds0.mm"
include "bitr3d.mm"
include "3imtr3d.mm"
include "divcan1d.mm"
include "mulid1d.mm"
include "3brtr4d.mm"
include "1zzd.mm"
include "dvdscmulr.mm"
include "syl112anc.mm"
include "gcdcld.mm"
include "dvds1.mm"
include "znunit.mm"
include "mpbird.mm"
include "eleq1.mm"
include "imbi12d.mm"
include "syl5ibrcom.mm"
include "rexlimdva.mm"
include "com23.mm"
include "mpdd.mm"
include "ssrdv.mm"
include "wss.mm"
include "unitrrg.mm"
include "eqssd.mm"

theorem znrrg
  let cU: class U
  let cE: class E
  let cN: class N
  let cY: class Y
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let cA: class A
  let cL: class L
  assume znchr.y: |- Y = ( Z/nZ ` N )
  assume znunit.u: |- U = ( Unit ` Y )
  assume znrrg.e: |- E = ( RLReg ` Y )


  assert |- ( N e. NN -> E = U )

  proof
    cN
    cn
    wcel
    #
    cE
    cU
    @0
    vx
    cE
    cU
    @0
    vx
    cv
    #
    cE
    wcel
    #
    @1
    vn
    cv
    #
    cY
    czrh
    cfv
    #
    cfv
    #
    wceq
    #
    vn
    cz
    wrex
    #
    @1
    cU
    wcel
    #
    @0
    @2
    @7
    @0
    cz
    cY
    cbs
    cfv
    #
    @4
    wfo
    #
    @1
    @9
    wcel
    @7
    @2
    @0
    cN
    cn0
    wcel
    #
    @10
    cN
    nnnn0
    #
    @9
    @4
    cN
    cY
    znchr.y
    @9
    eqid
    #
    @4
    eqid
    #
    znzrhfo
    #
    syl
    cE
    @9
    @1
    @9
    cY
    cE
    znrrg.e
    @13
    rrgss
    sseli
    vn
    cz
    @9
    @1
    @4
    foelrn
    syl2an
    ex
    @0
    @7
    @2
    @8
    @0
    @6
    @2
    @8
    wi
    #
    vn
    cz
    @0
    @3
    cz
    wcel
    #
    wa
    #
    @16
    @6
    @5
    cE
    wcel
    #
    @5
    cU
    wcel
    #
    wi
    @18
    @19
    @20
    @18
    @19
    wa
    #
    @20
    @3
    cN
    cgcd
    co
    #
    c1
    wceq
    #
    @21
    @22
    c1
    cdvds
    wbr
    #
    @23
    @21
    cN
    @22
    cdiv
    co
    #
    @22
    cmul
    co
    #
    @25
    c1
    cmul
    co
    #
    cdvds
    wbr
    #
    @24
    @21
    cN
    @25
    @26
    @27
    cdvds
    @21
    cN
    @3
    @25
    cmul
    co
    #
    cdvds
    wbr
    #
    cN
    @25
    cdvds
    wbr
    #
    @21
    @22
    @25
    cmul
    co
    #
    cN
    @29
    cdvds
    @21
    cN
    @22
    @0
    cN
    cc
    wcel
    @17
    @19
    cN
    nncn
    ad2antrr
    #
    @21
    @22
    @21
    @17
    cN
    cz
    wcel
    #
    @3
    cc0
    wceq
    #
    cN
    cc0
    wceq
    #
    wa
    #
    wn
    #
    @22
    cn
    wcel
    #
    @0
    @17
    @19
    simplr
    #
    @0
    @34
    @17
    @19
    cN
    nnz
    ad2antrr
    #
    @21
    cN
    cc0
    wne
    #
    @38
    @0
    @42
    @17
    @19
    cN
    nnne0
    ad2antrr
    @37
    cN
    cc0
    @35
    @36
    simpr
    necon3ai
    syl
    @3
    cN
    gcdn0cl
    syl21anc
    #
    nncnd
    #
    @21
    @22
    @43
    nnne0d
    #
    divcan2d
    @21
    @22
    @3
    cdvds
    wbr
    #
    @32
    @29
    cdvds
    wbr
    #
    @21
    @46
    @22
    cN
    cdvds
    wbr
    #
    @21
    @17
    @34
    @46
    @48
    wa
    @40
    @41
    @3
    cN
    gcddvds
    syl2anc
    #
    simpld
    @21
    @22
    cz
    wcel
    #
    @17
    @25
    cz
    wcel
    #
    @46
    @47
    wi
    @21
    @22
    @43
    nnzd
    #
    @40
    @21
    @25
    @21
    @48
    @25
    cn
    wcel
    #
    @21
    @46
    @48
    @49
    simprd
    @21
    @0
    @39
    @48
    @53
    wb
    @0
    @17
    @19
    simpll
    @43
    cN
    @22
    nndivdvds
    syl2anc
    mpbid
    #
    nnzd
    #
    @25
    @22
    @3
    dvdsmulc
    syl3anc
    mpd
    eqbrtrrd
    @21
    @5
    @25
    @4
    cfv
    #
    cY
    cmulr
    cfv
    #
    co
    #
    cY
    c0g
    cfv
    #
    wceq
    #
    @56
    @59
    wceq
    #
    @30
    @31
    @21
    @19
    @56
    @9
    wcel
    @60
    @61
    wi
    @18
    @19
    simpr
    @21
    cz
    @9
    @25
    @4
    @21
    @10
    cz
    @9
    @4
    wf
    @21
    @11
    @10
    @0
    @11
    @17
    @19
    @12
    ad2antrr
    #
    @15
    syl
    cz
    @9
    @4
    fof
    syl
    @55
    ffvelrnd
    @9
    cY
    @57
    cE
    @5
    @56
    @59
    znrrg.e
    @13
    @57
    eqid
    #
    @59
    eqid
    #
    rrgeq0i
    syl2anc
    @21
    @29
    @4
    cfv
    #
    @59
    wceq
    #
    @60
    @30
    @21
    @65
    @58
    @59
    @21
    @4
    zring
    cY
    crh
    co
    wcel
    #
    @17
    @51
    @65
    @58
    wceq
    @21
    cY
    crg
    wcel
    #
    @67
    @0
    @68
    @17
    @19
    @0
    cY
    ccrg
    wcel
    #
    @68
    @0
    @11
    @69
    @12
    cN
    cY
    znchr.y
    zncrng
    syl
    cY
    crngring
    syl
    #
    ad2antrr
    cY
    @4
    @14
    zrhrhm
    syl
    @40
    @55
    @3
    @25
    zring
    cY
    cmul
    @57
    @4
    cz
    zringbas
    zringmulr
    @63
    rhmmul
    syl3anc
    eqeq1d
    @21
    @11
    @29
    cz
    wcel
    @66
    @30
    wb
    @62
    @21
    @3
    @25
    @40
    @55
    zmulcld
    @29
    @4
    cN
    cY
    @59
    znchr.y
    @14
    @64
    zndvds0
    syl2anc
    bitr3d
    @21
    @11
    @51
    @61
    @31
    wb
    @62
    @55
    @25
    @4
    cN
    cY
    @59
    znchr.y
    @14
    @64
    zndvds0
    syl2anc
    3imtr3d
    mpd
    @21
    cN
    @22
    @33
    @44
    @45
    divcan1d
    @21
    @25
    @21
    @25
    @54
    nncnd
    mulid1d
    3brtr4d
    @21
    @50
    c1
    cz
    wcel
    @51
    @25
    cc0
    wne
    @28
    @24
    wb
    @52
    @21
    1zzd
    @55
    @21
    @25
    @54
    nnne0d
    @25
    @22
    c1
    dvdscmulr
    syl112anc
    mpbid
    @21
    @22
    cn0
    wcel
    @24
    @23
    wb
    @21
    @3
    cN
    @40
    @41
    gcdcld
    @22
    dvds1
    syl
    mpbid
    @21
    @11
    @17
    @20
    @23
    wb
    @62
    @40
    @3
    cU
    @4
    cN
    cY
    znchr.y
    znunit.u
    @14
    znunit
    syl2anc
    mpbird
    ex
    @6
    @2
    @19
    @8
    @20
    @1
    @5
    cE
    eleq1
    @1
    @5
    cU
    eleq1
    imbi12d
    syl5ibrcom
    rexlimdva
    com23
    mpdd
    ssrdv
    @0
    @68
    cU
    cE
    wss
    @70
    cY
    cU
    cE
    znrrg.e
    znunit.u
    unitrrg
    syl
    eqssd
end
