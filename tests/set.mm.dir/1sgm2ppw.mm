include "cn.mm"
include "wcel.mm"
include "c1.mm"
include "c2.mm"
include "cmin.mm"
include "co.mm"
include "cexp.mm"
include "csgm.mm"
include "cc0.mm"
include "cfz.mm"
include "ccxp.mm"
include "cv.mm"
include "csu.mm"
include "cdiv.mm"
include "cc.mm"
include "cprime.mm"
include "cn0.mm"
include "wceq.mm"
include "ax-1cn.mm"
include "a1i.mm"
include "2prm.mm"
include "nnm1nn0.mm"
include "sgmppw.mm"
include "syl3anc.mm"
include "2cn.mm"
include "cxp1.mm"
include "mp1i.mm"
include "oveq1d.mm"
include "sumeq2i.mm"
include "wne.mm"
include "1ne2.mm"
include "necomi.mm"
include "nnnn0.mm"
include "geoser.mm"
include "syl5eq.mm"
include "cneg.mm"
include "2nn.mm"
include "nnexpcl.mm"
include "sylancr.mm"
include "nncnd.mm"
include "subcl.mm"
include "sylancl.mm"
include "ax-1ne0.mm"
include "div2negd.mm"
include "negsubdi2.mm"
include "caddc.mm"
include "df-neg.mm"
include "0cn.mm"
include "pnpcan.mm"
include "mp3an.mm"
include "1p0e1.mm"
include "1p1e2.mm"
include "oveq12i.mm"
include "3eqtr2i.mm"
include "oveq12d.mm"
include "div1d.mm"
include "3eqtr3d.mm"
include "3eqtrd.mm"

theorem 1sgm2ppw
  let cN: class N
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vn: setvar n
  let vx: setvar x
  let cA: class A
  let cM: class M
  let cP: class P
  let cK: class K


  assert |- ( N e. NN -> ( 1 sigma ( 2 ^ ( N - 1 ) ) ) = ( ( 2 ^ N ) - 1 ) )

  proof
    cN
    cn
    wcel
    #
    c1
    c2
    cN
    c1
    cmin
    co
    #
    cexp
    co
    csgm
    co
    #
    cc0
    @1
    cfz
    co
    #
    c2
    c1
    ccxp
    co
    #
    vk
    cv
    #
    cexp
    co
    #
    vk
    csu
    #
    c1
    c2
    cN
    cexp
    co
    #
    cmin
    co
    #
    c1
    c2
    cmin
    co
    #
    cdiv
    co
    #
    @8
    c1
    cmin
    co
    #
    @0
    c1
    cc
    wcel
    #
    c2
    cprime
    wcel
    #
    @1
    cn0
    wcel
    @2
    @7
    wceq
    @13
    @0
    ax-1cn
    a1i
    #
    @14
    @0
    2prm
    a1i
    cN
    nnm1nn0
    c1
    c2
    vk
    @1
    sgmppw
    syl3anc
    @0
    @7
    @3
    c2
    @5
    cexp
    co
    #
    vk
    csu
    @11
    @3
    @6
    @16
    vk
    @5
    @3
    wcel
    #
    @4
    c2
    @5
    cexp
    c2
    cc
    wcel
    #
    @4
    c2
    wceq
    @17
    2cn
    c2
    cxp1
    mp1i
    oveq1d
    sumeq2i
    @0
    c2
    vk
    cN
    @18
    @0
    2cn
    a1i
    c2
    c1
    wne
    @0
    c1
    c2
    1ne2
    necomi
    a1i
    cN
    nnnn0
    #
    geoser
    syl5eq
    @0
    @12
    cneg
    #
    c1
    cneg
    #
    cdiv
    co
    @12
    c1
    cdiv
    co
    @11
    @12
    @0
    @12
    c1
    @0
    @8
    cc
    wcel
    #
    @13
    @12
    cc
    wcel
    @0
    @8
    @0
    c2
    cn
    wcel
    cN
    cn0
    wcel
    @8
    cn
    wcel
    2nn
    @19
    c2
    cN
    nnexpcl
    sylancr
    nncnd
    #
    ax-1cn
    @8
    c1
    subcl
    sylancl
    #
    @15
    c1
    cc0
    wne
    @0
    ax-1ne0
    a1i
    div2negd
    @0
    @20
    @9
    @21
    @10
    cdiv
    @0
    @22
    @13
    @20
    @9
    wceq
    @23
    ax-1cn
    @8
    c1
    negsubdi2
    sylancl
    @21
    @10
    wceq
    @0
    @21
    cc0
    c1
    cmin
    co
    #
    c1
    cc0
    caddc
    co
    #
    c1
    c1
    caddc
    co
    #
    cmin
    co
    #
    @10
    c1
    df-neg
    @13
    cc0
    cc
    wcel
    @13
    @28
    @25
    wceq
    ax-1cn
    0cn
    ax-1cn
    c1
    cc0
    c1
    pnpcan
    mp3an
    @26
    c1
    @27
    c2
    cmin
    1p0e1
    1p1e2
    oveq12i
    3eqtr2i
    a1i
    oveq12d
    @0
    @12
    @24
    div1d
    3eqtr3d
    3eqtrd
end
