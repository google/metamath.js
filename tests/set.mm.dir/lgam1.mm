include "caddc.mm"
include "c1.mm"
include "cuz.mm"
include "cfv.mm"
include "cc0.mm"
include "csn.mm"
include "cxp.mm"
include "cseq.mm"
include "clgam.mm"
include "cli.mm"
include "wbr.mm"
include "wceq.mm"
include "clog.mm"
include "co.mm"
include "wtru.mm"
include "cn.mm"
include "cv.mm"
include "cdiv.mm"
include "cmul.mm"
include "cmin.mm"
include "cmpt.mm"
include "wcel.mm"
include "peano2nn.mm"
include "nnrpd.mm"
include "nnrp.mm"
include "rpdivcld.mm"
include "relogcld.mm"
include "recnd.mm"
include "mulid2d.mm"
include "nncn.mm"
include "nnne0.mm"
include "dividd.mm"
include "oveq1d.mm"
include "1cnd.mm"
include "divdird.mm"
include "reccld.mm"
include "addcomd.mm"
include "3eqtr4rd.mm"
include "fveq2d.mm"
include "oveq12d.mm"
include "subidd.mm"
include "eqtrd.mm"
include "mpteq2ia.mm"
include "fconstmpt.mm"
include "nnuz.mm"
include "xpeq1i.mm"
include "3eqtr2ri.mm"
include "cc.mm"
include "cz.mm"
include "cdif.mm"
include "wn.mm"
include "ax-1cn.mm"
include "1nn.mm"
include "eldifn.mm"
include "mt2.mm"
include "eldif.mm"
include "mpbir2an.mm"
include "a1i.mm"
include "lgamcvg.mm"
include "trud.mm"
include "log1.mm"
include "oveq2i.mm"
include "lgamcl.mm"
include "ax-mp.mm"
include "addid1i.mm"
include "eqtri.mm"
include "breqtri.mm"
include "1z.mm"
include "serclim0.mm"
include "climuni.mm"
include "mp2an.mm"

theorem lgam1
  let vm: setvar m


  assert |- ( log_G ` 1 ) = 0

  proof
    caddc
    c1
    cuz
    cfv
    #
    cc0
    csn
    #
    cxp
    #
    c1
    cseq
    #
    c1
    clgam
    cfv
    #
    cli
    wbr
    @3
    cc0
    cli
    wbr
    #
    @4
    cc0
    wceq
    @3
    @4
    c1
    clog
    cfv
    #
    caddc
    co
    #
    @4
    cli
    @3
    @7
    cli
    wbr
    wtru
    c1
    vm
    @2
    vm
    cn
    c1
    vm
    cv
    #
    c1
    caddc
    co
    #
    @8
    cdiv
    co
    #
    clog
    cfv
    #
    cmul
    co
    #
    c1
    @8
    cdiv
    co
    #
    c1
    caddc
    co
    #
    clog
    cfv
    #
    cmin
    co
    #
    cmpt
    vm
    cn
    cc0
    cmpt
    cn
    @1
    cxp
    @2
    vm
    cn
    @16
    cc0
    @8
    cn
    wcel
    #
    @16
    @11
    @11
    cmin
    co
    cc0
    @17
    @12
    @11
    @15
    @11
    cmin
    @17
    @11
    @17
    @11
    @17
    @10
    @17
    @9
    @8
    @17
    @9
    @8
    peano2nn
    nnrpd
    @8
    nnrp
    rpdivcld
    relogcld
    recnd
    #
    mulid2d
    @17
    @14
    @10
    clog
    @17
    @8
    @8
    cdiv
    co
    #
    @13
    caddc
    co
    c1
    @13
    caddc
    co
    @10
    @14
    @17
    @19
    c1
    @13
    caddc
    @17
    @8
    @8
    nncn
    #
    @8
    nnne0
    #
    dividd
    oveq1d
    @17
    @8
    c1
    @8
    @20
    @17
    1cnd
    #
    @20
    @21
    divdird
    @17
    @13
    c1
    @17
    @8
    @20
    @21
    reccld
    @22
    addcomd
    3eqtr4rd
    fveq2d
    oveq12d
    @17
    @11
    @18
    subidd
    eqtrd
    mpteq2ia
    vm
    cn
    cc0
    fconstmpt
    cn
    @0
    @1
    nnuz
    xpeq1i
    3eqtr2ri
    c1
    cc
    cz
    cn
    cdif
    #
    cdif
    wcel
    #
    wtru
    @24
    c1
    cc
    wcel
    c1
    @23
    wcel
    #
    wn
    ax-1cn
    @25
    c1
    cn
    wcel
    1nn
    c1
    cz
    cn
    eldifn
    mt2
    c1
    cc
    @23
    eldif
    mpbir2an
    #
    a1i
    lgamcvg
    trud
    @7
    @4
    cc0
    caddc
    co
    @4
    @6
    cc0
    @4
    caddc
    log1
    oveq2i
    @4
    @24
    @4
    cc
    wcel
    @26
    c1
    lgamcl
    ax-mp
    addid1i
    eqtri
    breqtri
    c1
    cz
    wcel
    @5
    1z
    c1
    serclim0
    ax-mp
    @4
    cc0
    @3
    climuni
    mp2an
end
