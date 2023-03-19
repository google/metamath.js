include "cn.mm"
include "wcel.mm"
include "cz.mm"
include "cgcd.mm"
include "co.mm"
include "c1.mm"
include "wceq.mm"
include "w3a.mm"
include "cphi.mm"
include "cfv.mm"
include "cfz.mm"
include "cv.mm"
include "cc0.mm"
include "cfzo.mm"
include "crab.mm"
include "wf1o.mm"
include "cexp.mm"
include "cmo.mm"
include "cen.mm"
include "wbr.mm"
include "wex.mm"
include "chash.mm"
include "cn0.mm"
include "phicl.mm"
include "nnnn0d.mm"
include "hashfz1.mm"
include "syl.mm"
include "dfphi2.mm"
include "eqtrd.mm"
include "3ad2ant1.mm"
include "cfn.mm"
include "wb.mm"
include "fzfi.mm"
include "wss.mm"
include "fzofi.mm"
include "ssrab2.mm"
include "ssfi.mm"
include "mp2an.mm"
include "hashen.mm"
include "sylib.mm"
include "bren.mm"
include "wa.mm"
include "cmul.mm"
include "cmpt.mm"
include "simpl.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "cbvrabv.mm"
include "eqid.mm"
include "simpr.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "oveq1d.mm"
include "cbvmptv.mm"
include "eulerthlem2.mm"
include "exlimddv.mm"

theorem eulerth
  let cA: class A
  let cN: class N
  let vf: setvar f
  let vk: setvar k
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( N e. NN /\ A e. ZZ /\ ( A gcd N ) = 1 ) -> ( ( A ^ ( phi ` N ) ) mod N ) = ( 1 mod N ) )

  proof
    cN
    cn
    wcel
    #
    cA
    cz
    wcel
    #
    cA
    cN
    cgcd
    co
    c1
    wceq
    #
    w3a
    #
    c1
    cN
    cphi
    cfv
    #
    cfz
    co
    #
    vk
    cv
    #
    cN
    cgcd
    co
    #
    c1
    wceq
    #
    vk
    cc0
    cN
    cfzo
    co
    #
    crab
    #
    vf
    cv
    #
    wf1o
    #
    cA
    @4
    cexp
    co
    cN
    cmo
    co
    c1
    cN
    cmo
    co
    wceq
    vf
    @3
    @5
    @10
    cen
    wbr
    #
    @12
    vf
    wex
    @3
    @5
    chash
    cfv
    #
    @10
    chash
    cfv
    #
    wceq
    #
    @13
    @0
    @1
    @16
    @2
    @0
    @14
    @4
    @15
    @0
    @4
    cn0
    wcel
    @14
    @4
    wceq
    @0
    @4
    cN
    phicl
    nnnn0d
    @4
    hashfz1
    syl
    vk
    cN
    dfphi2
    eqtrd
    3ad2ant1
    @5
    cfn
    wcel
    @10
    cfn
    wcel
    #
    @16
    @13
    wb
    c1
    @4
    fzfi
    @9
    cfn
    wcel
    @10
    @9
    wss
    @17
    cc0
    cN
    fzofi
    @8
    vk
    @9
    ssrab2
    @9
    @10
    ssfi
    mp2an
    @5
    @10
    hashen
    mp2an
    sylib
    @5
    @10
    vf
    bren
    sylib
    @3
    @12
    wa
    vx
    vy
    cA
    @10
    @5
    @11
    vk
    @5
    cA
    @6
    @11
    cfv
    #
    cmul
    co
    #
    cN
    cmo
    co
    #
    cmpt
    cN
    @3
    @12
    simpl
    @8
    vy
    cv
    #
    cN
    cgcd
    co
    #
    c1
    wceq
    vk
    vy
    @9
    @6
    @21
    wceq
    @7
    @22
    c1
    @6
    @21
    cN
    cgcd
    oveq1
    eqeq1d
    cbvrabv
    @5
    eqid
    @3
    @12
    simpr
    vk
    vx
    @5
    @20
    cA
    vx
    cv
    #
    @11
    cfv
    #
    cmul
    co
    #
    cN
    cmo
    co
    @6
    @23
    wceq
    #
    @19
    @25
    cN
    cmo
    @26
    @18
    @24
    cA
    cmul
    @6
    @23
    @11
    fveq2
    oveq2d
    oveq1d
    cbvmptv
    eulerthlem2
    exlimddv
end
