include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "cbc.mm"
include "cmin.mm"
include "cdiv.mm"
include "cmul.mm"
include "wceq.mm"
include "cz.mm"
include "wb.mm"
include "elfzel1.mm"
include "elfzel2.mm"
include "elfzelz.mm"
include "1zzd.mm"
include "fzaddel.mm"
include "syl22anc.mm"
include "ibi.mm"
include "1e0p1.mm"
include "oveq1i.mm"
include "syl6eleqr.mm"
include "bcm1k.mm"
include "syl.mm"
include "cc.mm"
include "zcnd.mm"
include "ax-1cn.mm"
include "pncan.mm"
include "sylancl.mm"
include "oveq2d.mm"
include "bcp1n.mm"
include "eqtrd.mm"
include "oveq1d.mm"
include "oveq12d.mm"
include "bcrpcl.mm"
include "rpcnd.mm"
include "peano2zd.mm"
include "zred.mm"
include "clt.mm"
include "wbr.mm"
include "cn.mm"
include "elfzle2.mm"
include "ltp1d.mm"
include "lelttrd.mm"
include "znnsub.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "nndivred.mm"
include "recnd.mm"
include "nnred.mm"
include "cn0.mm"
include "elfznn0.mm"
include "nn0p1nn.mm"
include "mulassd.mm"
include "nncnd.mm"
include "nnne0d.mm"
include "dmdcan2d.mm"

theorem bcp1nk
  let cK: class K
  let cN: class N


  assert |- ( K e. ( 0 ... N ) -> ( ( N + 1 ) _C ( K + 1 ) ) = ( ( N _C K ) x. ( ( N + 1 ) / ( K + 1 ) ) ) )

  proof
    cK
    cc0
    cN
    cfz
    co
    wcel
    #
    cN
    c1
    caddc
    co
    #
    cK
    c1
    caddc
    co
    #
    cbc
    co
    #
    @1
    @2
    c1
    cmin
    co
    #
    cbc
    co
    #
    @1
    @4
    cmin
    co
    #
    @2
    cdiv
    co
    #
    cmul
    co
    #
    cN
    cK
    cbc
    co
    #
    @1
    @2
    cdiv
    co
    #
    cmul
    co
    #
    @0
    @2
    c1
    @1
    cfz
    co
    #
    wcel
    @3
    @8
    wceq
    @0
    @2
    cc0
    c1
    caddc
    co
    #
    @1
    cfz
    co
    #
    @12
    @0
    @2
    @14
    wcel
    #
    @0
    cc0
    cz
    wcel
    cN
    cz
    wcel
    cK
    cz
    wcel
    #
    c1
    cz
    wcel
    @0
    @15
    wb
    cK
    cc0
    cN
    elfzel1
    cK
    cc0
    cN
    elfzel2
    #
    cK
    cc0
    cN
    elfzelz
    #
    @0
    1zzd
    cK
    c1
    cc0
    cN
    fzaddel
    syl22anc
    ibi
    c1
    @13
    @1
    cfz
    1e0p1
    oveq1i
    syl6eleqr
    @2
    @1
    bcm1k
    syl
    @0
    @8
    @9
    @1
    @1
    cK
    cmin
    co
    #
    cdiv
    co
    #
    cmul
    co
    #
    @19
    @2
    cdiv
    co
    #
    cmul
    co
    #
    @11
    @0
    @5
    @21
    @7
    @22
    cmul
    @0
    @5
    @1
    cK
    cbc
    co
    @21
    @0
    @4
    cK
    @1
    cbc
    @0
    cK
    cc
    wcel
    c1
    cc
    wcel
    @4
    cK
    wceq
    @0
    cK
    @18
    zcnd
    ax-1cn
    cK
    c1
    pncan
    sylancl
    #
    oveq2d
    cK
    cN
    bcp1n
    eqtrd
    @0
    @6
    @19
    @2
    cdiv
    @0
    @4
    cK
    @1
    cmin
    @24
    oveq2d
    oveq1d
    oveq12d
    @0
    @23
    @9
    @20
    @22
    cmul
    co
    #
    cmul
    co
    @11
    @0
    @9
    @20
    @22
    @0
    @9
    cK
    cN
    bcrpcl
    rpcnd
    @0
    @20
    @0
    @1
    @19
    @0
    @1
    @0
    cN
    @17
    peano2zd
    #
    zred
    #
    @0
    cK
    @1
    clt
    wbr
    #
    @19
    cn
    wcel
    #
    @0
    cK
    cN
    @1
    @0
    cK
    @18
    zred
    @0
    cN
    @17
    zred
    #
    @27
    cK
    cc0
    cN
    elfzle2
    @0
    cN
    @30
    ltp1d
    lelttrd
    @0
    @16
    @1
    cz
    wcel
    @28
    @29
    wb
    @18
    @26
    cK
    @1
    znnsub
    syl2anc
    mpbid
    #
    nndivred
    recnd
    @0
    @22
    @0
    @19
    @2
    @0
    @19
    @31
    nnred
    @0
    cK
    cn0
    wcel
    @2
    cn
    wcel
    cK
    cN
    elfznn0
    cK
    nn0p1nn
    syl
    #
    nndivred
    recnd
    mulassd
    @0
    @25
    @10
    @9
    cmul
    @0
    @1
    @19
    @2
    @0
    @1
    @26
    zcnd
    @0
    @19
    @31
    nncnd
    @0
    @2
    @32
    nncnd
    @0
    @19
    @31
    nnne0d
    @0
    @2
    @32
    nnne0d
    dmdcan2d
    oveq2d
    eqtrd
    eqtrd
    eqtrd
end
