include "cply.mm"
include "cfv.mm"
include "wcel.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "ccn.mm"
include "co.mm"
include "cc.mm"
include "ccncf.mm"
include "cc0.mm"
include "cdgr.mm"
include "cfz.mm"
include "cv.mm"
include "ccoe.mm"
include "cexp.mm"
include "cmul.mm"
include "csu.mm"
include "cmpt.mm"
include "eqid.mm"
include "coeid.mm"
include "ctopon.mm"
include "cnfldtopon.mm"
include "a1i.mm"
include "fzfid.mm"
include "wa.mm"
include "cn0.mm"
include "wf.mm"
include "coef3.mm"
include "elfznn0.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "cnmptc.mm"
include "adantl.mm"
include "expcn.mm"
include "syl.mm"
include "ctx.mm"
include "mulcn.mm"
include "cnmpt12f.mm"
include "fsumcn.mm"
include "eqeltrd.mm"
include "cncfcn1.mm"
include "syl6eleqr.mm"

theorem plycn
  let cS: class S
  let cF: class F
  let vk: setvar k
  let vz: setvar z
  let cA: class A
  let cN: class N


  assert |- ( F e. ( Poly ` S ) -> F e. ( CC -cn-> CC ) )

  proof
    cF
    cS
    cply
    cfv
    wcel
    #
    cF
    ccnfld
    ctopn
    cfv
    #
    @1
    ccn
    co
    #
    cc
    cc
    ccncf
    co
    @0
    cF
    vz
    cc
    cc0
    cF
    cdgr
    cfv
    #
    cfz
    co
    #
    vk
    cv
    #
    cF
    ccoe
    cfv
    #
    cfv
    #
    vz
    cv
    @5
    cexp
    co
    #
    cmul
    co
    #
    vk
    csu
    cmpt
    @2
    vz
    @6
    cS
    vk
    cF
    @3
    @6
    eqid
    #
    @3
    eqid
    coeid
    @0
    vz
    @4
    @9
    vk
    @1
    @1
    cc
    @1
    eqid
    #
    @1
    cc
    ctopon
    cfv
    wcel
    #
    @0
    @1
    @11
    cnfldtopon
    #
    a1i
    @0
    cc0
    @3
    fzfid
    @0
    @5
    @4
    wcel
    #
    wa
    #
    vz
    @7
    @8
    cmul
    @1
    @1
    @1
    @1
    cc
    @12
    @15
    @13
    a1i
    #
    @15
    vz
    @7
    @1
    @1
    cc
    cc
    @16
    @16
    @0
    cn0
    cc
    @6
    wf
    @5
    cn0
    wcel
    #
    @7
    cc
    wcel
    @14
    @6
    cS
    cF
    @10
    coef3
    @5
    @3
    elfznn0
    #
    cn0
    cc
    @5
    @6
    ffvelrn
    syl2an
    cnmptc
    @15
    @17
    vz
    cc
    @8
    cmpt
    @2
    wcel
    @14
    @17
    @0
    @18
    adantl
    vz
    @1
    @5
    @11
    expcn
    syl
    cmul
    @1
    @1
    ctx
    co
    @1
    ccn
    co
    wcel
    @15
    @1
    @11
    mulcn
    a1i
    cnmpt12f
    fsumcn
    eqeltrd
    @1
    @11
    cncfcn1
    syl6eleqr
end
