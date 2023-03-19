include "cn0.mm"
include "wcel.mm"
include "cn.mm"
include "cxp.mm"
include "cpw.mm"
include "cvdwa.mm"
include "cfv.mm"
include "wf.mm"
include "cc0.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cfz.mm"
include "cv.mm"
include "cmul.mm"
include "caddc.mm"
include "cmpt.mm"
include "crn.mm"
include "cmpt2.mm"
include "wral.mm"
include "wa.mm"
include "wss.mm"
include "simpll.mm"
include "elfznn0.mm"
include "adantl.mm"
include "nnnn0.mm"
include "ad2antlr.mm"
include "nn0mulcld.mm"
include "nnnn0addcl.mm"
include "syl2anc.mm"
include "eqid.mm"
include "fmptd.mm"
include "frn.mm"
include "syl.mm"
include "nnex.mm"
include "elpw2.mm"
include "sylibr.mm"
include "rgen2a.mm"
include "fmpt2.mm"
include "mpbi.mm"
include "vdwapfval.mm"
include "feq1d.mm"
include "mpbiri.mm"

theorem vdwapf
  let cK: class K
  let va: setvar a
  let vd: setvar d
  let vm: setvar m
  let vn: setvar n
  let vx: setvar x
  let cA: class A
  let cD: class D
  let vk: setvar k
  let cX: class X


  assert |- ( K e. NN0 -> ( AP ` K ) : ( NN X. NN ) --> ~P NN )

  proof
    cK
    cn0
    wcel
    #
    cn
    cn
    cxp
    #
    cn
    cpw
    #
    cK
    cvdwa
    cfv
    #
    wf
    @1
    @2
    va
    vd
    cn
    cn
    vm
    cc0
    cK
    c1
    cmin
    co
    #
    cfz
    co
    #
    va
    cv
    #
    vm
    cv
    #
    vd
    cv
    #
    cmul
    co
    #
    caddc
    co
    #
    cmpt
    #
    crn
    #
    cmpt2
    #
    wf
    #
    @12
    @2
    wcel
    #
    vd
    cn
    wral
    va
    cn
    wral
    @14
    @15
    va
    vd
    cn
    @6
    cn
    wcel
    #
    @8
    cn
    wcel
    #
    wa
    #
    @12
    cn
    wss
    #
    @15
    @18
    @5
    cn
    @11
    wf
    @19
    @18
    vm
    @5
    @10
    cn
    @11
    @18
    @7
    @5
    wcel
    #
    wa
    #
    @16
    @9
    cn0
    wcel
    @10
    cn
    wcel
    @16
    @17
    @20
    simpll
    @21
    @7
    @8
    @20
    @7
    cn0
    wcel
    @18
    @7
    @4
    elfznn0
    adantl
    @17
    @8
    cn0
    wcel
    @16
    @20
    @8
    nnnn0
    ad2antlr
    nn0mulcld
    @6
    @9
    nnnn0addcl
    syl2anc
    @11
    eqid
    fmptd
    @5
    cn
    @11
    frn
    syl
    @12
    cn
    nnex
    elpw2
    sylibr
    rgen2a
    va
    vd
    cn
    cn
    @12
    @2
    @13
    @13
    eqid
    fmpt2
    mpbi
    @0
    @1
    @2
    @3
    @13
    vm
    cK
    va
    vd
    vdwapfval
    feq1d
    mpbiri
end
