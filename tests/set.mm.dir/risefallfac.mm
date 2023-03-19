include "cc.mm"
include "wcel.mm"
include "cn0.mm"
include "wa.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "cmin.mm"
include "caddc.mm"
include "cprod.mm"
include "cneg.mm"
include "cmul.mm"
include "crisefac.mm"
include "cexp.mm"
include "cfallfac.mm"
include "negcl.mm"
include "adantr.mm"
include "cn.mm"
include "elfznn.mm"
include "nnm1nn0.mm"
include "syl.mm"
include "nn0cnd.mm"
include "subcl.mm"
include "syl2an.mm"
include "mulm1d.mm"
include "simpll.mm"
include "adantl.mm"
include "negdi2d.mm"
include "negeqd.mm"
include "simpl.mm"
include "addcl.mm"
include "negnegd.mm"
include "3eqtr2rd.mm"
include "prodeq2dv.mm"
include "risefacval2.mm"
include "wceq.mm"
include "chash.mm"
include "cfv.mm"
include "cfn.mm"
include "fzfi.mm"
include "neg1cn.mm"
include "fprodconst.mm"
include "mp2an.mm"
include "hashfz1.mm"
include "oveq2d.mm"
include "syl5req.mm"
include "fallfacval2.mm"
include "sylan.mm"
include "oveq12d.mm"
include "fzfid.mm"
include "a1i.mm"
include "fprodmul.mm"
include "eqtr4d.mm"
include "3eqtr4d.mm"

theorem risefallfac
  let cN: class N
  let cX: class X
  let vk: setvar k


  assert |- ( ( X e. CC /\ N e. NN0 ) -> ( X RiseFac N ) = ( ( -u 1 ^ N ) x. ( -u X FallFac N ) ) )

  proof
    cX
    cc
    wcel
    #
    cN
    cn0
    wcel
    #
    wa
    #
    c1
    cN
    cfz
    co
    #
    cX
    vk
    cv
    #
    c1
    cmin
    co
    #
    caddc
    co
    #
    vk
    cprod
    @3
    c1
    cneg
    #
    cX
    cneg
    #
    @5
    cmin
    co
    #
    cmul
    co
    #
    vk
    cprod
    #
    cX
    cN
    crisefac
    co
    @7
    cN
    cexp
    co
    #
    @8
    cN
    cfallfac
    co
    #
    cmul
    co
    #
    @2
    @3
    @6
    @10
    vk
    @2
    @4
    @3
    wcel
    #
    wa
    #
    @10
    @9
    cneg
    @6
    cneg
    #
    cneg
    @6
    @16
    @9
    @2
    @8
    cc
    wcel
    #
    @5
    cc
    wcel
    #
    @9
    cc
    wcel
    @15
    @0
    @18
    @1
    cX
    negcl
    #
    adantr
    @15
    @5
    @15
    @4
    cn
    wcel
    @5
    cn0
    wcel
    @4
    cN
    elfznn
    @4
    nnm1nn0
    syl
    nn0cnd
    #
    @8
    @5
    subcl
    syl2an
    #
    mulm1d
    @16
    @17
    @9
    @16
    cX
    @5
    @0
    @1
    @15
    simpll
    @15
    @19
    @2
    @21
    adantl
    negdi2d
    negeqd
    @16
    @6
    @2
    @0
    @19
    @6
    cc
    wcel
    @15
    @0
    @1
    simpl
    @21
    cX
    @5
    addcl
    syl2an
    negnegd
    3eqtr2rd
    prodeq2dv
    cX
    vk
    cN
    risefacval2
    @2
    @14
    @3
    @7
    vk
    cprod
    #
    @3
    @9
    vk
    cprod
    #
    cmul
    co
    @11
    @2
    @12
    @23
    @13
    @24
    cmul
    @1
    @12
    @23
    wceq
    @0
    @1
    @23
    @7
    @3
    chash
    cfv
    #
    cexp
    co
    #
    @12
    @3
    cfn
    wcel
    @7
    cc
    wcel
    #
    @23
    @26
    wceq
    c1
    cN
    fzfi
    neg1cn
    @3
    @7
    vk
    fprodconst
    mp2an
    @1
    @25
    cN
    @7
    cexp
    cN
    hashfz1
    oveq2d
    syl5req
    adantl
    @0
    @18
    @1
    @13
    @24
    wceq
    @20
    @8
    vk
    cN
    fallfacval2
    sylan
    oveq12d
    @2
    @3
    @7
    @9
    vk
    @2
    c1
    cN
    fzfid
    @27
    @16
    neg1cn
    a1i
    @22
    fprodmul
    eqtr4d
    3eqtr4d
end
