include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "cn.mm"
include "crab.mm"
include "ccxp.mm"
include "co.mm"
include "csu.mm"
include "cc.mm"
include "wcel.mm"
include "wral.mm"
include "cxp.mm"
include "csgm.mm"
include "wf.mm"
include "wa.mm"
include "c1.mm"
include "cfz.mm"
include "cfn.mm"
include "wss.mm"
include "fzfid.mm"
include "dvdsssfz1.mm"
include "adantl.mm"
include "ssfi.mm"
include "syl2anc.mm"
include "elrabi.mm"
include "nncnd.mm"
include "simpl.mm"
include "cxpcl.mm"
include "syl2anr.mm"
include "fsumcl.mm"
include "rgen2.mm"
include "df-sgm.mm"
include "fmpt2.mm"
include "mpbi.mm"

theorem sgmf
  let vk: setvar k
  let vn: setvar n
  let vp: setvar p
  let vq: setvar q
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cK: class K
  let cM: class M
  let cN: class N
  let cS: class S
  let cB: class B
  let cP: class P


  assert |- sigma : ( CC X. NN ) --> CC

  proof
    vp
    cv
    vn
    cv
    #
    cdvds
    wbr
    #
    vp
    cn
    crab
    #
    vk
    cv
    #
    vx
    cv
    #
    ccxp
    co
    #
    vk
    csu
    #
    cc
    wcel
    #
    vn
    cn
    wral
    vx
    cc
    wral
    cc
    cn
    cxp
    cc
    csgm
    wf
    @7
    vx
    vn
    cc
    cn
    @4
    cc
    wcel
    #
    @0
    cn
    wcel
    #
    wa
    #
    @2
    @5
    vk
    @10
    c1
    @0
    cfz
    co
    #
    cfn
    wcel
    @2
    @11
    wss
    #
    @2
    cfn
    wcel
    @10
    c1
    @0
    fzfid
    @9
    @12
    @8
    @0
    vp
    dvdsssfz1
    adantl
    @11
    @2
    ssfi
    syl2anc
    @3
    @2
    wcel
    #
    @3
    cc
    wcel
    @8
    @5
    cc
    wcel
    @10
    @13
    @3
    @1
    vp
    @3
    cn
    elrabi
    nncnd
    @8
    @9
    simpl
    @3
    @4
    cxpcl
    syl2anr
    fsumcl
    rgen2
    vx
    vn
    cc
    cn
    @6
    cc
    csgm
    vx
    vk
    vn
    vp
    df-sgm
    fmpt2
    mpbi
end
