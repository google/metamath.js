include "cc.mm"
include "wcel.mm"
include "cprime.mm"
include "cn0.mm"
include "w3a.mm"
include "cexp.mm"
include "co.mm"
include "csgm.mm"
include "cv.mm"
include "cdvds.mm"
include "wbr.mm"
include "cn.mm"
include "crab.mm"
include "ccxp.mm"
include "csu.mm"
include "cc0.mm"
include "cfz.mm"
include "wceq.mm"
include "simp1.mm"
include "simp2.mm"
include "prmnn.mm"
include "syl.mm"
include "simp3.mm"
include "nnexpcld.mm"
include "sgmval.mm"
include "syl2anc.mm"
include "cmpt.mm"
include "oveq1.mm"
include "fzfid.mm"
include "wf1o.mm"
include "eqid.mm"
include "dvdsppwf1o.mm"
include "cfv.mm"
include "oveq2.mm"
include "ovex.mm"
include "fvmpt.mm"
include "adantl.mm"
include "elrabi.mm"
include "nncnd.mm"
include "cxpcl.mm"
include "syl2anr.mm"
include "fsumf1o.mm"
include "wa.mm"
include "cmul.mm"
include "elfznn0.mm"
include "nn0cnd.mm"
include "adantr.mm"
include "mulcomd.mm"
include "oveq2d.mm"
include "nnrpd.mm"
include "nn0red.mm"
include "cxpmuld.mm"
include "cxpexp.mm"
include "oveq1d.mm"
include "eqtrd.mm"
include "cxpmul2d.mm"
include "3eqtr3d.mm"
include "sumeq2dv.mm"
include "3eqtrd.mm"

theorem sgmppw
  let cA: class A
  let cP: class P
  let vk: setvar k
  let cN: class N
  let vi: setvar i
  let vj: setvar j
  let vn: setvar n
  let vx: setvar x
  let cM: class M
  let cK: class K

  disjoint A k
  disjoint N k
  disjoint P k
  disjoint i j
  disjoint i k
  disjoint i n
  disjoint i x
  disjoint A i
  disjoint j k
  disjoint j n
  disjoint j x
  disjoint A j
  disjoint k n
  disjoint k x
  disjoint n x
  disjoint A n
  disjoint A x
  disjoint M i
  disjoint M j
  disjoint M k
  disjoint M x
  disjoint N i
  disjoint N j
  disjoint N n
  disjoint N x
  disjoint P i
  disjoint P n
  disjoint P x
  disjoint K n
  disjoint K x
  assert |- ( ( A e. CC /\ P e. Prime /\ N e. NN0 ) -> ( A sigma ( P ^ N ) ) = sum_ k e. ( 0 ... N ) ( ( P ^c A ) ^ k ) )

  proof
    cA
    cc
    wcel
    #
    cP
    cprime
    wcel
    #
    cN
    cn0
    wcel
    #
    w3a
    #
    cA
    cP
    cN
    cexp
    co
    #
    csgm
    co
    #
    vx
    cv
    @4
    cdvds
    wbr
    #
    vx
    cn
    crab
    #
    vn
    cv
    #
    cA
    ccxp
    co
    #
    vn
    csu
    #
    cc0
    cN
    cfz
    co
    #
    cP
    vk
    cv
    #
    cexp
    co
    #
    cA
    ccxp
    co
    #
    vk
    csu
    @11
    cP
    cA
    ccxp
    co
    @12
    cexp
    co
    #
    vk
    csu
    @3
    @0
    @4
    cn
    wcel
    @5
    @10
    wceq
    @0
    @1
    @2
    simp1
    #
    @3
    cP
    cN
    @3
    @1
    cP
    cn
    wcel
    #
    @0
    @1
    @2
    simp2
    #
    cP
    prmnn
    syl
    #
    @0
    @1
    @2
    simp3
    #
    nnexpcld
    cA
    @4
    vn
    vx
    sgmval
    syl2anc
    @3
    @7
    @9
    @11
    @14
    vn
    vk
    vi
    @11
    cP
    vi
    cv
    #
    cexp
    co
    #
    cmpt
    #
    @13
    @8
    @13
    cA
    ccxp
    oveq1
    @3
    cc0
    cN
    fzfid
    @3
    @1
    @2
    @11
    @7
    @23
    wf1o
    @18
    @20
    vx
    cN
    cP
    vi
    @23
    @23
    eqid
    #
    dvdsppwf1o
    syl2anc
    @12
    @11
    wcel
    #
    @12
    @23
    cfv
    @13
    wceq
    @3
    vi
    @12
    @22
    @13
    @11
    @23
    @21
    @12
    cP
    cexp
    oveq2
    @24
    cP
    @12
    cexp
    ovex
    fvmpt
    adantl
    @8
    @7
    wcel
    #
    @8
    cc
    wcel
    @0
    @9
    cc
    wcel
    @3
    @26
    @8
    @6
    vx
    @8
    cn
    elrabi
    nncnd
    @16
    @8
    cA
    cxpcl
    syl2anr
    fsumf1o
    @3
    @11
    @14
    @15
    vk
    @3
    @25
    wa
    #
    cP
    @12
    cA
    cmul
    co
    #
    ccxp
    co
    #
    cP
    cA
    @12
    cmul
    co
    #
    ccxp
    co
    @14
    @15
    @27
    @28
    @30
    cP
    ccxp
    @27
    @12
    cA
    @27
    @12
    @25
    @12
    cn0
    wcel
    #
    @3
    @12
    cN
    elfznn0
    adantl
    #
    nn0cnd
    @3
    @0
    @25
    @16
    adantr
    #
    mulcomd
    oveq2d
    @27
    @29
    cP
    @12
    ccxp
    co
    #
    cA
    ccxp
    co
    @14
    @27
    cP
    @12
    cA
    @27
    cP
    @3
    @17
    @25
    @19
    adantr
    #
    nnrpd
    @27
    @12
    @32
    nn0red
    @33
    cxpmuld
    @27
    @34
    @13
    cA
    ccxp
    @27
    cP
    cc
    wcel
    @31
    @34
    @13
    wceq
    @27
    cP
    @35
    nncnd
    #
    @32
    cP
    @12
    cxpexp
    syl2anc
    oveq1d
    eqtrd
    @27
    cP
    cA
    @12
    @36
    @33
    @32
    cxpmul2d
    3eqtr3d
    sumeq2dv
    3eqtrd
end
