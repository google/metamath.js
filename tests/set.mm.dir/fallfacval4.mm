include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "wcel.mm"
include "c1.mm"
include "cmin.mm"
include "cv.mm"
include "cprod.mm"
include "cdiv.mm"
include "cfallfac.mm"
include "cfa.mm"
include "cfv.mm"
include "caddc.mm"
include "cmul.mm"
include "fzfid.mm"
include "cc.mm"
include "elfzelz.mm"
include "zcnd.mm"
include "adantl.mm"
include "fprodcl.mm"
include "wa.mm"
include "cn.mm"
include "elfznn.mm"
include "nncnd.mm"
include "nnne0d.mm"
include "fprodn0.mm"
include "divcan3d.mm"
include "clt.mm"
include "wbr.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "fznn0sub.mm"
include "nn0red.mm"
include "ltp1d.mm"
include "fzdisj.mm"
include "syl.mm"
include "cuz.mm"
include "cun.mm"
include "cn0.mm"
include "nn0p1nn.mm"
include "nnuz.mm"
include "syl6eleq.mm"
include "cz.mm"
include "cle.mm"
include "nn0zd.mm"
include "elfzel2.mm"
include "elfzle1.mm"
include "zred.mm"
include "subge02d.mm"
include "mpbid.mm"
include "eluz2.mm"
include "syl3anbrc.mm"
include "fzsplit2.mm"
include "syl2anc.mm"
include "fprodsplit.mm"
include "oveq1d.mm"
include "1cnd.mm"
include "subsubd.mm"
include "prodeq1d.mm"
include "3eqtr4rd.mm"
include "fallfacval3.mm"
include "elfz3nn0.mm"
include "fprodfac.mm"
include "oveq12d.mm"
include "3eqtr4d.mm"

theorem fallfacval4
  let cA: class A
  let cN: class N
  let vk: setvar k


  assert |- ( N e. ( 0 ... A ) -> ( A FallFac N ) = ( ( ! ` A ) / ( ! ` ( A - N ) ) ) )

  proof
    cN
    cc0
    cA
    cfz
    co
    wcel
    #
    cA
    cN
    c1
    cmin
    co
    cmin
    co
    #
    cA
    cfz
    co
    #
    vk
    cv
    #
    vk
    cprod
    #
    c1
    cA
    cfz
    co
    #
    @3
    vk
    cprod
    #
    c1
    cA
    cN
    cmin
    co
    #
    cfz
    co
    #
    @3
    vk
    cprod
    #
    cdiv
    co
    #
    cA
    cN
    cfallfac
    co
    cA
    cfa
    cfv
    #
    @7
    cfa
    cfv
    #
    cdiv
    co
    @0
    @9
    @7
    c1
    caddc
    co
    #
    cA
    cfz
    co
    #
    @3
    vk
    cprod
    #
    cmul
    co
    #
    @9
    cdiv
    co
    @15
    @10
    @4
    @0
    @15
    @9
    @0
    @14
    @3
    vk
    @0
    @13
    cA
    fzfid
    @3
    @14
    wcel
    #
    @3
    cc
    wcel
    #
    @0
    @17
    @3
    @3
    @13
    cA
    elfzelz
    zcnd
    adantl
    fprodcl
    @0
    @8
    @3
    vk
    @0
    c1
    @7
    fzfid
    #
    @0
    @3
    @8
    wcel
    #
    wa
    #
    @3
    @20
    @3
    cn
    wcel
    @0
    @3
    @7
    elfznn
    adantl
    #
    nncnd
    #
    fprodcl
    @0
    @8
    @3
    vk
    @19
    @23
    @21
    @3
    @22
    nnne0d
    fprodn0
    divcan3d
    @0
    @6
    @16
    @9
    cdiv
    @0
    @8
    @14
    @3
    @5
    vk
    @0
    @7
    @13
    clt
    wbr
    @8
    @14
    cin
    c0
    wceq
    @0
    @7
    @0
    @7
    cN
    cc0
    cA
    fznn0sub
    #
    nn0red
    ltp1d
    c1
    @7
    @13
    cA
    fzdisj
    syl
    @0
    @13
    c1
    cuz
    cfv
    #
    wcel
    cA
    @7
    cuz
    cfv
    wcel
    #
    @5
    @8
    @14
    cun
    wceq
    @0
    @13
    cn
    @25
    @0
    @7
    cn0
    wcel
    #
    @13
    cn
    wcel
    @24
    @7
    nn0p1nn
    syl
    nnuz
    syl6eleq
    @0
    @7
    cz
    wcel
    cA
    cz
    wcel
    @7
    cA
    cle
    wbr
    #
    @26
    @0
    @7
    @24
    nn0zd
    cN
    cc0
    cA
    elfzel2
    #
    @0
    cc0
    cN
    cle
    wbr
    @28
    cN
    cc0
    cA
    elfzle1
    @0
    cA
    cN
    @0
    cA
    @29
    zred
    @0
    cN
    cN
    cc0
    cA
    elfzelz
    #
    zred
    subge02d
    mpbid
    @7
    cA
    eluz2
    syl3anbrc
    @7
    c1
    cA
    fzsplit2
    syl2anc
    @0
    c1
    cA
    fzfid
    @3
    @5
    wcel
    #
    @18
    @0
    @31
    @3
    @3
    cA
    elfznn
    nncnd
    adantl
    fprodsplit
    oveq1d
    @0
    @2
    @14
    @3
    vk
    @0
    @1
    @13
    cA
    cfz
    @0
    cA
    cN
    c1
    @0
    cA
    @29
    zcnd
    @0
    cN
    @30
    zcnd
    @0
    1cnd
    subsubd
    oveq1d
    prodeq1d
    3eqtr4rd
    cA
    vk
    cN
    fallfacval3
    @0
    @11
    @6
    @12
    @9
    cdiv
    @0
    cA
    cn0
    wcel
    @11
    @6
    wceq
    cN
    cA
    elfz3nn0
    cA
    vk
    fprodfac
    syl
    @0
    @27
    @12
    @9
    wceq
    @24
    @7
    vk
    fprodfac
    syl
    oveq12d
    3eqtr4d
end
