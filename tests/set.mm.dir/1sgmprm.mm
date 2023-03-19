include "cprime.mm"
include "wcel.mm"
include "c1.mm"
include "cexp.mm"
include "co.mm"
include "csgm.mm"
include "cc0.mm"
include "cfz.mm"
include "ccxp.mm"
include "cv.mm"
include "csu.mm"
include "caddc.mm"
include "cc.mm"
include "cn0.mm"
include "wceq.mm"
include "ax-1cn.mm"
include "1nn0.mm"
include "sgmppw.mm"
include "mp3an13.mm"
include "prmnn.mm"
include "nncnd.mm"
include "exp1d.mm"
include "oveq2d.mm"
include "wa.mm"
include "adantr.mm"
include "cxp1d.mm"
include "oveq1d.mm"
include "sumeq2dv.mm"
include "cmin.mm"
include "1m1e0.mm"
include "oveq2i.mm"
include "sumeq1i.mm"
include "cz.mm"
include "0z.mm"
include "exp0d.mm"
include "syl6eqel.mm"
include "oveq2.mm"
include "fsum1.mm"
include "sylancr.mm"
include "eqtrd.mm"
include "syl5eq.mm"
include "oveq12d.mm"
include "cuz.mm"
include "cfv.mm"
include "a1i.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "elfznn0.mm"
include "expcl.mm"
include "syl2an.mm"
include "fsumm1.mm"
include "addcom.mm"
include "sylancl.mm"
include "3eqtr4d.mm"
include "3eqtr3d.mm"

theorem 1sgmprm
  let cP: class P
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vn: setvar n
  let vx: setvar x
  let cA: class A
  let cM: class M
  let cN: class N
  let cK: class K


  assert |- ( P e. Prime -> ( 1 sigma P ) = ( P + 1 ) )

  proof
    cP
    cprime
    wcel
    #
    c1
    cP
    c1
    cexp
    co
    #
    csgm
    co
    #
    cc0
    c1
    cfz
    co
    #
    cP
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
    cP
    csgm
    co
    cP
    c1
    caddc
    co
    #
    c1
    cc
    wcel
    #
    @0
    c1
    cn0
    wcel
    #
    @2
    @7
    wceq
    ax-1cn
    1nn0
    c1
    cP
    vk
    c1
    sgmppw
    mp3an13
    @0
    @1
    cP
    c1
    csgm
    @0
    cP
    @0
    cP
    cP
    prmnn
    nncnd
    #
    exp1d
    #
    oveq2d
    @0
    @7
    @3
    cP
    @5
    cexp
    co
    #
    vk
    csu
    #
    @8
    @0
    @3
    @6
    @13
    vk
    @0
    @5
    @3
    wcel
    #
    wa
    #
    @4
    cP
    @5
    cexp
    @16
    cP
    @0
    cP
    cc
    wcel
    #
    @15
    @11
    adantr
    cxp1d
    oveq1d
    sumeq2dv
    @0
    cc0
    c1
    c1
    cmin
    co
    #
    cfz
    co
    #
    @13
    vk
    csu
    #
    @1
    caddc
    co
    c1
    cP
    caddc
    co
    #
    @14
    @8
    @0
    @20
    c1
    @1
    cP
    caddc
    @0
    @20
    cc0
    cc0
    cfz
    co
    #
    @13
    vk
    csu
    #
    c1
    @19
    @22
    @13
    vk
    @18
    cc0
    cc0
    cfz
    1m1e0
    oveq2i
    sumeq1i
    @0
    @23
    cP
    cc0
    cexp
    co
    #
    c1
    @0
    cc0
    cz
    wcel
    @24
    cc
    wcel
    @23
    @24
    wceq
    0z
    @0
    @24
    c1
    cc
    @0
    cP
    @11
    exp0d
    #
    ax-1cn
    syl6eqel
    @13
    @24
    vk
    cc0
    @5
    cc0
    cP
    cexp
    oveq2
    fsum1
    sylancr
    @25
    eqtrd
    syl5eq
    @12
    oveq12d
    @0
    @13
    @1
    vk
    cc0
    c1
    @0
    c1
    cn0
    cc0
    cuz
    cfv
    @10
    @0
    1nn0
    a1i
    nn0uz
    syl6eleq
    @0
    @17
    @5
    cn0
    wcel
    @13
    cc
    wcel
    @15
    @11
    @5
    c1
    elfznn0
    cP
    @5
    expcl
    syl2an
    @5
    c1
    cP
    cexp
    oveq2
    fsumm1
    @0
    @17
    @9
    @8
    @21
    wceq
    @11
    ax-1cn
    cP
    c1
    addcom
    sylancl
    3eqtr4d
    eqtrd
    3eqtr3d
end
