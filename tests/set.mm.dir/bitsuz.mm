include "cz.mm"
include "wcel.mm"
include "cn0.mm"
include "wa.mm"
include "c2.mm"
include "cexp.mm"
include "co.mm"
include "cdvds.mm"
include "wbr.mm"
include "cbits.mm"
include "cfv.mm"
include "cuz.mm"
include "cin.mm"
include "wceq.mm"
include "wss.mm"
include "cdiv.mm"
include "cfl.mm"
include "cmul.mm"
include "bitsres.mm"
include "eqeq1d.mm"
include "wb.mm"
include "simpl.mm"
include "zred.mm"
include "cn.mm"
include "2nn.mm"
include "a1i.mm"
include "simpr.mm"
include "nnexpcld.mm"
include "nndivred.mm"
include "flcld.mm"
include "nnzd.mm"
include "zmulcld.mm"
include "cpw.mm"
include "wf1.mm"
include "bitsf1.mm"
include "f1fveq.mm"
include "mpan.mm"
include "syl2anc.mm"
include "dvdsmul2.mm"
include "breq2.mm"
include "syl5ibcom.mm"
include "cc0.mm"
include "wne.mm"
include "nnne0d.mm"
include "dvdsval2.mm"
include "syl3anc.mm"
include "biimpa.mm"
include "flid.mm"
include "syl.mm"
include "oveq1d.mm"
include "cc.mm"
include "zcnd.mm"
include "adantr.mm"
include "nncnd.mm"
include "2cnd.mm"
include "2ne0.mm"
include "nn0zd.mm"
include "expne0d.mm"
include "divcan1d.mm"
include "eqtrd.mm"
include "ex.mm"
include "impbid.mm"
include "3bitrrd.mm"
include "df-ss.mm"
include "syl6bbr.mm"

theorem bitsuz
  let cA: class A
  let cN: class N


  assert |- ( ( A e. ZZ /\ N e. NN0 ) -> ( ( 2 ^ N ) || A <-> ( bits ` A ) C_ ( ZZ>= ` N ) ) )

  proof
    cA
    cz
    wcel
    #
    cN
    cn0
    wcel
    #
    wa
    #
    c2
    cN
    cexp
    co
    #
    cA
    cdvds
    wbr
    #
    cA
    cbits
    cfv
    #
    cN
    cuz
    cfv
    #
    cin
    #
    @5
    wceq
    #
    @5
    @6
    wss
    @2
    @8
    cA
    @3
    cdiv
    co
    #
    cfl
    cfv
    #
    @3
    cmul
    co
    #
    cbits
    cfv
    #
    @5
    wceq
    #
    @11
    cA
    wceq
    #
    @4
    @2
    @7
    @12
    @5
    cA
    cN
    bitsres
    eqeq1d
    @2
    @11
    cz
    wcel
    #
    @0
    @13
    @14
    wb
    #
    @2
    @10
    @3
    @2
    @9
    @2
    cA
    @3
    @2
    cA
    @0
    @1
    simpl
    #
    zred
    @2
    c2
    cN
    c2
    cn
    wcel
    @2
    2nn
    a1i
    @0
    @1
    simpr
    #
    nnexpcld
    #
    nndivred
    flcld
    #
    @2
    @3
    @19
    nnzd
    #
    zmulcld
    @17
    cz
    cn0
    cpw
    #
    cbits
    wf1
    @15
    @0
    wa
    @16
    bitsf1
    cz
    @22
    @11
    cA
    cbits
    f1fveq
    mpan
    syl2anc
    @2
    @14
    @4
    @2
    @3
    @11
    cdvds
    wbr
    #
    @14
    @4
    @2
    @10
    cz
    wcel
    @3
    cz
    wcel
    #
    @23
    @20
    @21
    @10
    @3
    dvdsmul2
    syl2anc
    @11
    cA
    @3
    cdvds
    breq2
    syl5ibcom
    @2
    @4
    @14
    @2
    @4
    wa
    #
    @11
    @9
    @3
    cmul
    co
    cA
    @25
    @10
    @9
    @3
    cmul
    @25
    @9
    cz
    wcel
    #
    @10
    @9
    wceq
    @2
    @4
    @26
    @2
    @24
    @3
    cc0
    wne
    @0
    @4
    @26
    wb
    @21
    @2
    @3
    @19
    nnne0d
    @17
    @3
    cA
    dvdsval2
    syl3anc
    biimpa
    @9
    flid
    syl
    oveq1d
    @25
    cA
    @3
    @2
    cA
    cc
    wcel
    @4
    @2
    cA
    @17
    zcnd
    adantr
    @2
    @3
    cc
    wcel
    @4
    @2
    @3
    @19
    nncnd
    adantr
    @25
    c2
    cN
    @25
    2cnd
    c2
    cc0
    wne
    @25
    2ne0
    a1i
    @2
    cN
    cz
    wcel
    @4
    @2
    cN
    @18
    nn0zd
    adantr
    expne0d
    divcan1d
    eqtrd
    ex
    impbid
    3bitrrd
    @5
    @6
    df-ss
    syl6bbr
end
