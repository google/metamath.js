include "cn0.mm"
include "wcel.mm"
include "c2.mm"
include "cfmtno.mm"
include "cfv.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "cv.mm"
include "cmul.mm"
include "co.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "cz.mm"
include "wrex.mm"
include "cexp.mm"
include "cmin.mm"
include "cn.mm"
include "2nn.mm"
include "a1i.mm"
include "id.mm"
include "nnexpcld.mm"
include "nnm1nn0.mm"
include "syl.mm"
include "nnzd.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "fmtno.mm"
include "eqeqan12rd.mm"
include "2cnd.mm"
include "nncnd.mm"
include "mulcomd.mm"
include "cc.mm"
include "expm1t.mm"
include "syl2anc.mm"
include "eqtr4d.mm"
include "rspcedvd.mm"
include "wb.mm"
include "fmtnonn.mm"
include "odd2np1.mm"
include "mpbird.mm"

theorem fmtnoodd
  let cN: class N
  let vk: setvar k
  let vx: setvar x


  assert |- ( N e. NN0 -> -. 2 || ( FermatNo ` N ) )

  proof
    cN
    cn0
    wcel
    #
    c2
    cN
    cfmtno
    cfv
    #
    cdvds
    wbr
    wn
    #
    c2
    vk
    cv
    #
    cmul
    co
    #
    c1
    caddc
    co
    #
    @1
    wceq
    #
    vk
    cz
    wrex
    #
    @0
    @6
    c2
    c2
    c2
    cN
    cexp
    co
    #
    c1
    cmin
    co
    #
    cexp
    co
    #
    cmul
    co
    #
    c1
    caddc
    co
    #
    c2
    @8
    cexp
    co
    #
    c1
    caddc
    co
    #
    wceq
    vk
    @10
    cz
    @0
    @10
    @0
    c2
    @9
    c2
    cn
    wcel
    @0
    2nn
    a1i
    #
    @0
    @8
    cn
    wcel
    #
    @9
    cn0
    wcel
    @0
    c2
    cN
    @15
    @0
    id
    nnexpcld
    #
    @8
    nnm1nn0
    syl
    nnexpcld
    #
    nnzd
    @3
    @10
    wceq
    #
    @0
    @5
    @12
    @1
    @14
    @19
    @4
    @11
    c1
    caddc
    @3
    @10
    c2
    cmul
    oveq2
    oveq1d
    cN
    fmtno
    eqeqan12rd
    @0
    @11
    @13
    c1
    caddc
    @0
    @11
    @10
    c2
    cmul
    co
    #
    @13
    @0
    c2
    @10
    @0
    2cnd
    #
    @0
    @10
    @18
    nncnd
    mulcomd
    @0
    c2
    cc
    wcel
    @16
    @13
    @20
    wceq
    @21
    @17
    c2
    @8
    expm1t
    syl2anc
    eqtr4d
    oveq1d
    rspcedvd
    @0
    @1
    cz
    wcel
    @2
    @7
    wb
    @0
    @1
    cN
    fmtnonn
    nnzd
    vk
    @1
    odd2np1
    syl
    mpbird
end
