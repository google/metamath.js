include "cz.mm"
include "wcel.mm"
include "cn0.mm"
include "wa.mm"
include "c2.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cexp.mm"
include "cdiv.mm"
include "cfl.mm"
include "cfv.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "cbits.mm"
include "cmul.mm"
include "cn.mm"
include "2nn.mm"
include "a1i.mm"
include "nncnd.mm"
include "simpr.mm"
include "expp1d.mm"
include "nnexpcld.mm"
include "mulcomd.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "simpl.mm"
include "zcnd.mm"
include "nnne0d.mm"
include "divdiv1d.mm"
include "eqtr4d.mm"
include "fveq2d.mm"
include "cr.mm"
include "wceq.mm"
include "zred.mm"
include "rehalfcld.mm"
include "fldiv.mm"
include "syl2anc.mm"
include "breq2d.mm"
include "notbid.mm"
include "wb.mm"
include "peano2nn0.mm"
include "bitsval2.mm"
include "sylan2.mm"
include "flcld.mm"
include "sylancom.mm"
include "3bitr4d.mm"

theorem bitsp1
  let cM: class M
  let cN: class N


  assert |- ( ( N e. ZZ /\ M e. NN0 ) -> ( ( M + 1 ) e. ( bits ` N ) <-> M e. ( bits ` ( |_ ` ( N / 2 ) ) ) ) )

  proof
    cN
    cz
    wcel
    #
    cM
    cn0
    wcel
    #
    wa
    #
    c2
    cN
    c2
    cM
    c1
    caddc
    co
    #
    cexp
    co
    #
    cdiv
    co
    #
    cfl
    cfv
    #
    cdvds
    wbr
    #
    wn
    #
    c2
    cN
    c2
    cdiv
    co
    #
    cfl
    cfv
    #
    c2
    cM
    cexp
    co
    #
    cdiv
    co
    cfl
    cfv
    #
    cdvds
    wbr
    #
    wn
    #
    @3
    cN
    cbits
    cfv
    wcel
    #
    cM
    @10
    cbits
    cfv
    wcel
    #
    @2
    @7
    @13
    @2
    @6
    @12
    c2
    cdvds
    @2
    @6
    @9
    @11
    cdiv
    co
    #
    cfl
    cfv
    #
    @12
    @2
    @5
    @17
    cfl
    @2
    @5
    cN
    c2
    @11
    cmul
    co
    #
    cdiv
    co
    @17
    @2
    @4
    @19
    cN
    cdiv
    @2
    @4
    @11
    c2
    cmul
    co
    @19
    @2
    c2
    cM
    @2
    c2
    c2
    cn
    wcel
    @2
    2nn
    a1i
    #
    nncnd
    #
    @0
    @1
    simpr
    #
    expp1d
    @2
    @11
    c2
    @2
    @11
    @2
    c2
    cM
    @20
    @22
    nnexpcld
    #
    nncnd
    #
    @21
    mulcomd
    eqtrd
    oveq2d
    @2
    cN
    c2
    @11
    @2
    cN
    @0
    @1
    simpl
    #
    zcnd
    @21
    @24
    @2
    c2
    @20
    nnne0d
    @2
    @11
    @23
    nnne0d
    divdiv1d
    eqtr4d
    fveq2d
    @2
    @9
    cr
    wcel
    @11
    cn
    wcel
    @12
    @18
    wceq
    @2
    cN
    @2
    cN
    @25
    zred
    rehalfcld
    #
    @23
    @9
    @11
    fldiv
    syl2anc
    eqtr4d
    breq2d
    notbid
    @1
    @0
    @3
    cn0
    wcel
    @15
    @8
    wb
    cM
    peano2nn0
    @3
    cN
    bitsval2
    sylan2
    @0
    @1
    @10
    cz
    wcel
    @16
    @14
    wb
    @2
    @9
    @26
    flcld
    cM
    @10
    bitsval2
    sylancom
    3bitr4d
end
