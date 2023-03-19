include "cz.mm"
include "wcel.mm"
include "cn0.mm"
include "cuz.mm"
include "cfv.mm"
include "w3a.mm"
include "cexp.mm"
include "co.mm"
include "cmin.mm"
include "cmul.mm"
include "cdvds.mm"
include "wbr.mm"
include "simp1.mm"
include "uznn0sub.mm"
include "3ad2ant3.mm"
include "zexpcl.mm"
include "syl2anc.mm"
include "3adant3.mm"
include "dvdsmul2.mm"
include "caddc.mm"
include "zcnd.mm"
include "simp2.mm"
include "expaddd.mm"
include "cc.mm"
include "eluzelcn.mm"
include "nn0cnd.mm"
include "npcand.mm"
include "oveq2d.mm"
include "eqtr3d.mm"
include "breqtrd.mm"

theorem dvdsexp
  let cA: class A
  let cM: class M
  let cN: class N


  assert |- ( ( A e. ZZ /\ M e. NN0 /\ N e. ( ZZ>= ` M ) ) -> ( A ^ M ) || ( A ^ N ) )

  proof
    cA
    cz
    wcel
    #
    cM
    cn0
    wcel
    #
    cN
    cM
    cuz
    cfv
    wcel
    #
    w3a
    #
    cA
    cM
    cexp
    co
    #
    cA
    cN
    cM
    cmin
    co
    #
    cexp
    co
    #
    @4
    cmul
    co
    #
    cA
    cN
    cexp
    co
    #
    cdvds
    @3
    @6
    cz
    wcel
    #
    @4
    cz
    wcel
    #
    @4
    @7
    cdvds
    wbr
    @3
    @0
    @5
    cn0
    wcel
    #
    @9
    @0
    @1
    @2
    simp1
    #
    @2
    @0
    @11
    @1
    cM
    cN
    uznn0sub
    3ad2ant3
    #
    cA
    @5
    zexpcl
    syl2anc
    @0
    @1
    @10
    @2
    cA
    cM
    zexpcl
    3adant3
    @6
    @4
    dvdsmul2
    syl2anc
    @3
    cA
    @5
    cM
    caddc
    co
    #
    cexp
    co
    @7
    @8
    @3
    cA
    @5
    cM
    @3
    cA
    @12
    zcnd
    @0
    @1
    @2
    simp2
    #
    @13
    expaddd
    @3
    @14
    cN
    cA
    cexp
    @3
    cN
    cM
    @2
    @0
    cN
    cc
    wcel
    @1
    cM
    cN
    eluzelcn
    3ad2ant3
    @3
    cM
    @15
    nn0cnd
    npcand
    oveq2d
    eqtr3d
    breqtrd
end
