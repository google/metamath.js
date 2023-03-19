include "cn0.mm"
include "wcel.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cprmo.mm"
include "cfv.mm"
include "cfz.mm"
include "cv.mm"
include "cprime.mm"
include "cif.mm"
include "cprod.mm"
include "cmin.mm"
include "cmul.mm"
include "wceq.mm"
include "peano2nn0.mm"
include "prmoval.mm"
include "syl.mm"
include "cn.mm"
include "cuz.mm"
include "nn0p1nn.mm"
include "elnnuz.mm"
include "sylib.mm"
include "wa.mm"
include "cc.mm"
include "elfzelz.mm"
include "zcnd.mm"
include "adantl.mm"
include "1cnd.mm"
include "ifcld.mm"
include "eleq1.mm"
include "id.mm"
include "ifbieq1d.mm"
include "fprodm1.mm"
include "nn0cn.mm"
include "pncan1.mm"
include "oveq2d.mm"
include "prodeq1d.mm"
include "oveq1d.mm"
include "eqcomd.mm"
include "wb.mm"
include "iftrue.mm"
include "eqeq12d.mm"
include "adantr.mm"
include "mpbird.mm"
include "wn.mm"
include "fzfid.mm"
include "elfznn.mm"
include "1nn.mm"
include "a1i.mm"
include "fprodnncl.mm"
include "nncnd.mm"
include "mulid1d.mm"
include "eqtr4d.mm"
include "iffalse.mm"
include "pm2.61ian.mm"
include "eqtrd.mm"
include "3eqtrd.mm"

theorem prmop1
  let cN: class N
  let vk: setvar k


  assert |- ( N e. NN0 -> ( #p ` ( N + 1 ) ) = if ( ( N + 1 ) e. Prime , ( ( #p ` N ) x. ( N + 1 ) ) , ( #p ` N ) ) )

  proof
    cN
    cn0
    wcel
    #
    cN
    c1
    caddc
    co
    #
    cprmo
    cfv
    #
    c1
    @1
    cfz
    co
    #
    vk
    cv
    #
    cprime
    wcel
    #
    @4
    c1
    cif
    #
    vk
    cprod
    #
    c1
    @1
    c1
    cmin
    co
    #
    cfz
    co
    #
    @6
    vk
    cprod
    #
    @1
    cprime
    wcel
    #
    @1
    c1
    cif
    #
    cmul
    co
    #
    @11
    cN
    cprmo
    cfv
    #
    @1
    cmul
    co
    #
    @14
    cif
    #
    @0
    @1
    cn0
    wcel
    @2
    @7
    wceq
    cN
    peano2nn0
    vk
    @1
    prmoval
    syl
    @0
    @6
    @12
    vk
    c1
    @1
    @0
    @1
    cn
    wcel
    @1
    c1
    cuz
    cfv
    wcel
    cN
    nn0p1nn
    @1
    elnnuz
    sylib
    @0
    @4
    @3
    wcel
    #
    wa
    #
    @5
    @4
    c1
    cc
    @17
    @4
    cc
    wcel
    @0
    @17
    @4
    @4
    c1
    @1
    elfzelz
    zcnd
    adantl
    @18
    1cnd
    ifcld
    @4
    @1
    wceq
    #
    @5
    @11
    @4
    @1
    c1
    @4
    @1
    cprime
    eleq1
    @19
    id
    ifbieq1d
    fprodm1
    @0
    @13
    c1
    cN
    cfz
    co
    #
    @6
    vk
    cprod
    #
    @12
    cmul
    co
    #
    @16
    @0
    @10
    @21
    @12
    cmul
    @0
    @9
    @20
    @6
    vk
    @0
    @8
    cN
    c1
    cfz
    @0
    cN
    cc
    wcel
    @8
    cN
    wceq
    cN
    nn0cn
    cN
    pncan1
    syl
    oveq2d
    prodeq1d
    oveq1d
    @11
    @0
    @22
    @16
    wceq
    #
    @11
    @0
    wa
    #
    @23
    @21
    @1
    cmul
    co
    #
    @15
    wceq
    #
    @24
    @21
    @14
    @1
    cmul
    @0
    @21
    @14
    wceq
    @11
    @0
    @14
    @21
    vk
    cN
    prmoval
    #
    eqcomd
    adantl
    oveq1d
    @11
    @23
    @26
    wb
    @0
    @11
    @22
    @25
    @16
    @15
    @11
    @12
    @1
    @21
    cmul
    @11
    @1
    c1
    iftrue
    oveq2d
    @11
    @15
    @14
    iftrue
    eqeq12d
    adantr
    mpbird
    @11
    wn
    #
    @0
    wa
    #
    @23
    @21
    c1
    cmul
    co
    #
    @14
    wceq
    #
    @29
    @30
    @21
    @14
    @29
    @21
    @0
    @21
    cc
    wcel
    @28
    @0
    @21
    @0
    @20
    @6
    vk
    @0
    c1
    cN
    fzfid
    @4
    @20
    wcel
    #
    @6
    cn
    wcel
    @0
    @32
    @5
    @4
    c1
    cn
    @4
    cN
    elfznn
    c1
    cn
    wcel
    @32
    1nn
    a1i
    ifcld
    adantl
    fprodnncl
    nncnd
    adantl
    mulid1d
    @0
    @14
    @21
    wceq
    @28
    @27
    adantl
    eqtr4d
    @28
    @23
    @31
    wb
    @0
    @28
    @22
    @30
    @16
    @14
    @28
    @12
    c1
    @21
    cmul
    @11
    @1
    c1
    iffalse
    oveq2d
    @11
    @15
    @14
    iffalse
    eqeq12d
    adantr
    mpbird
    pm2.61ian
    eqtrd
    3eqtrd
end
