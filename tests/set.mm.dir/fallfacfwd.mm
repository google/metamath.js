include "cc.mm"
include "wcel.mm"
include "cn.mm"
include "wa.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfallfac.mm"
include "cmin.mm"
include "cmul.mm"
include "cc0.mm"
include "cfz.mm"
include "cv.mm"
include "cprod.mm"
include "cn0.mm"
include "wceq.mm"
include "peano2cn.mm"
include "nnnn0.mm"
include "fallfacval.mm"
include "syl2an.mm"
include "cneg.mm"
include "0p1e1.mm"
include "oveq1i.mm"
include "prodeq1i.mm"
include "oveq2i.mm"
include "cuz.mm"
include "cfv.mm"
include "nnm1nn0.mm"
include "adantl.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "simpll.mm"
include "cz.mm"
include "elfzelz.mm"
include "peano2zm.mm"
include "syl.mm"
include "zcnd.mm"
include "subcld.mm"
include "oveq1.mm"
include "df-neg.mm"
include "syl6eqr.mm"
include "oveq2d.mm"
include "fprod1p.mm"
include "fallfacval2.mm"
include "sylan2.mm"
include "3eqtr4a.mm"
include "elfznn0.mm"
include "nn0cnd.mm"
include "1cnd.mm"
include "subsub3d.mm"
include "prodeq2dv.mm"
include "simpl.mm"
include "subnegd.mm"
include "oveq1d.mm"
include "3eqtr3d.mm"
include "eqtrd.mm"
include "simpr.mm"
include "nncnd.mm"
include "npcand.mm"
include "fallfacp1.mm"
include "eqtr3d.mm"
include "oveq12d.mm"
include "fallfaccl.mm"
include "mulcomd.mm"
include "adantr.mm"
include "subdird.mm"
include "pnncand.mm"
include "pncan3d.mm"
include "3eqtr2d.mm"

theorem fallfacfwd
  let cA: class A
  let cN: class N
  let vk: setvar k


  assert |- ( ( A e. CC /\ N e. NN ) -> ( ( ( A + 1 ) FallFac N ) - ( A FallFac N ) ) = ( N x. ( A FallFac ( N - 1 ) ) ) )

  proof
    cA
    cc
    wcel
    #
    cN
    cn
    wcel
    #
    wa
    #
    cA
    c1
    caddc
    co
    #
    cN
    cfallfac
    co
    #
    cA
    cN
    cfallfac
    co
    #
    cmin
    co
    @3
    cA
    cN
    c1
    cmin
    co
    #
    cfallfac
    co
    #
    cmul
    co
    #
    @7
    cA
    @6
    cmin
    co
    #
    cmul
    co
    #
    cmin
    co
    #
    cN
    @7
    cmul
    co
    #
    @2
    @4
    @8
    @5
    @10
    cmin
    @2
    @4
    cc0
    @6
    cfz
    co
    #
    @3
    vk
    cv
    #
    cmin
    co
    #
    vk
    cprod
    #
    @8
    @0
    @3
    cc
    wcel
    #
    cN
    cn0
    wcel
    @4
    @16
    wceq
    @1
    cA
    peano2cn
    #
    cN
    nnnn0
    @3
    vk
    cN
    fallfacval
    syl2an
    @2
    @13
    cA
    @14
    c1
    cmin
    co
    #
    cmin
    co
    #
    vk
    cprod
    #
    cA
    c1
    cneg
    #
    cmin
    co
    #
    @7
    cmul
    co
    #
    @16
    @8
    @2
    @23
    cc0
    c1
    caddc
    co
    #
    @6
    cfz
    co
    #
    @20
    vk
    cprod
    #
    cmul
    co
    @23
    c1
    @6
    cfz
    co
    #
    @20
    vk
    cprod
    #
    cmul
    co
    @21
    @24
    @27
    @29
    @23
    cmul
    @26
    @28
    @20
    vk
    @25
    c1
    @6
    cfz
    0p1e1
    oveq1i
    prodeq1i
    oveq2i
    @2
    @20
    @23
    vk
    cc0
    @6
    @2
    @6
    cn0
    cc0
    cuz
    cfv
    @1
    @6
    cn0
    wcel
    #
    @0
    cN
    nnm1nn0
    #
    adantl
    #
    nn0uz
    syl6eleq
    @2
    @14
    @13
    wcel
    #
    wa
    #
    cA
    @19
    @0
    @1
    @33
    simpll
    #
    @34
    @19
    @34
    @14
    cz
    wcel
    #
    @19
    cz
    wcel
    @33
    @36
    @2
    @14
    cc0
    @6
    elfzelz
    adantl
    @14
    peano2zm
    syl
    zcnd
    subcld
    @14
    cc0
    wceq
    #
    @19
    @22
    cA
    cmin
    @37
    @19
    cc0
    c1
    cmin
    co
    @22
    @14
    cc0
    c1
    cmin
    oveq1
    c1
    df-neg
    syl6eqr
    oveq2d
    fprod1p
    @2
    @7
    @29
    @23
    cmul
    @1
    @0
    @30
    @7
    @29
    wceq
    @31
    cA
    vk
    @6
    fallfacval2
    sylan2
    oveq2d
    3eqtr4a
    @2
    @13
    @20
    @15
    vk
    @34
    cA
    @14
    c1
    @35
    @34
    @14
    @33
    @14
    cn0
    wcel
    @2
    @14
    @6
    elfznn0
    adantl
    nn0cnd
    @34
    1cnd
    subsub3d
    prodeq2dv
    @2
    @23
    @3
    @7
    cmul
    @2
    cA
    c1
    @0
    @1
    simpl
    #
    @2
    1cnd
    #
    subnegd
    oveq1d
    3eqtr3d
    eqtrd
    @2
    cA
    @6
    c1
    caddc
    co
    #
    cfallfac
    co
    #
    @5
    @10
    @2
    @40
    cN
    cA
    cfallfac
    @2
    cN
    c1
    @2
    cN
    @0
    @1
    simpr
    nncnd
    #
    @39
    npcand
    oveq2d
    @1
    @0
    @30
    @41
    @10
    wceq
    @31
    cA
    @6
    fallfacp1
    sylan2
    eqtr3d
    oveq12d
    @2
    @11
    @8
    @9
    @7
    cmul
    co
    #
    cmin
    co
    @3
    @9
    cmin
    co
    #
    @7
    cmul
    co
    @12
    @2
    @10
    @43
    @8
    cmin
    @2
    @7
    @9
    @1
    @0
    @30
    @7
    cc
    wcel
    @31
    cA
    @6
    fallfaccl
    sylan2
    #
    @2
    cA
    @6
    @38
    @2
    @6
    @32
    nn0cnd
    #
    subcld
    #
    mulcomd
    oveq2d
    @2
    @3
    @9
    @7
    @0
    @17
    @1
    @18
    adantr
    @47
    @45
    subdird
    @2
    @44
    cN
    @7
    cmul
    @2
    @44
    c1
    @6
    caddc
    co
    cN
    @2
    cA
    c1
    @6
    @38
    @39
    @46
    pnncand
    @2
    c1
    cN
    @39
    @42
    pncan3d
    eqtrd
    oveq1d
    3eqtr2d
    eqtrd
end
