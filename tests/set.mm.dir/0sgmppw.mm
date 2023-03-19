include "cprime.mm"
include "wcel.mm"
include "cn0.mm"
include "wa.mm"
include "cc0.mm"
include "cexp.mm"
include "co.mm"
include "csgm.mm"
include "cfz.mm"
include "chash.mm"
include "cfv.mm"
include "cmin.mm"
include "c1.mm"
include "caddc.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "cn.mm"
include "crab.mm"
include "wceq.mm"
include "prmnn.mm"
include "nnexpcl.mm"
include "sylan.mm"
include "0sgm.mm"
include "syl.mm"
include "cen.mm"
include "cfn.mm"
include "cvv.mm"
include "cmpt.mm"
include "wf1o.mm"
include "fzfid.mm"
include "nnex.mm"
include "rabex.mm"
include "a1i.mm"
include "eqid.mm"
include "dvdsppwf1o.mm"
include "f1oen2g.mm"
include "syl3anc.mm"
include "hasheni.mm"
include "eqtr4d.mm"
include "cuz.mm"
include "simpr.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "hashfz.mm"
include "cc.mm"
include "nn0cn.mm"
include "adantl.mm"
include "subid1d.mm"
include "oveq1d.mm"
include "3eqtrd.mm"

theorem 0sgmppw
  let cP: class P
  let cK: class K
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vn: setvar n
  let vx: setvar x
  let cA: class A
  let cM: class M
  let cN: class N


  assert |- ( ( P e. Prime /\ K e. NN0 ) -> ( 0 sigma ( P ^ K ) ) = ( K + 1 ) )

  proof
    cP
    cprime
    wcel
    #
    cK
    cn0
    wcel
    #
    wa
    #
    cc0
    cP
    cK
    cexp
    co
    #
    csgm
    co
    #
    cc0
    cK
    cfz
    co
    #
    chash
    cfv
    #
    cK
    cc0
    cmin
    co
    #
    c1
    caddc
    co
    #
    cK
    c1
    caddc
    co
    @2
    @4
    vx
    cv
    @3
    cdvds
    wbr
    #
    vx
    cn
    crab
    #
    chash
    cfv
    #
    @6
    @2
    @3
    cn
    wcel
    #
    @4
    @11
    wceq
    @0
    cP
    cn
    wcel
    @1
    @12
    cP
    prmnn
    cP
    cK
    nnexpcl
    sylan
    @3
    vx
    0sgm
    syl
    @2
    @5
    @10
    cen
    wbr
    #
    @6
    @11
    wceq
    @2
    @5
    cfn
    wcel
    @10
    cvv
    wcel
    #
    @5
    @10
    vn
    @5
    cP
    vn
    cv
    cexp
    co
    cmpt
    #
    wf1o
    @13
    @2
    cc0
    cK
    fzfid
    @14
    @2
    @9
    vx
    cn
    nnex
    rabex
    a1i
    vx
    cK
    cP
    vn
    @15
    @15
    eqid
    dvdsppwf1o
    @5
    @10
    @15
    cfn
    cvv
    f1oen2g
    syl3anc
    @5
    @10
    hasheni
    syl
    eqtr4d
    @2
    cK
    cc0
    cuz
    cfv
    #
    wcel
    @6
    @8
    wceq
    @2
    cK
    cn0
    @16
    @0
    @1
    simpr
    nn0uz
    syl6eleq
    cc0
    cK
    hashfz
    syl
    @2
    @7
    cK
    c1
    caddc
    @2
    cK
    @1
    cK
    cc
    wcel
    @0
    cK
    nn0cn
    adantl
    subid1d
    oveq1d
    3eqtrd
end
