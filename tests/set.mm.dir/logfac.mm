include "cn0.mm"
include "wcel.mm"
include "cn.mm"
include "cc0.mm"
include "wceq.mm"
include "wo.mm"
include "cfa.mm"
include "cfv.mm"
include "clog.mm"
include "c1.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "csu.mm"
include "elnn0.mm"
include "cmul.mm"
include "cid.mm"
include "cseq.mm"
include "caddc.mm"
include "crp.mm"
include "wa.mm"
include "rpmulcl.mm"
include "adantl.mm"
include "cvv.mm"
include "vex.mm"
include "fvi.mm"
include "ax-mp.mm"
include "elfznn.mm"
include "nnrpd.mm"
include "syl5eqel.mm"
include "cuz.mm"
include "elnnuz.mm"
include "biimpi.mm"
include "relogmul.mm"
include "fveq2i.mm"
include "a1i.mm"
include "seqhomo.mm"
include "facnn.mm"
include "fveq2d.mm"
include "eqidd.mm"
include "cr.mm"
include "relogcl.mm"
include "syl.mm"
include "recnd.mm"
include "fsumser.mm"
include "3eqtr4d.mm"
include "c0.mm"
include "log1.mm"
include "sum0.mm"
include "eqtr4i.mm"
include "fveq2.mm"
include "fac0.mm"
include "syl6eq.mm"
include "oveq2.mm"
include "fz10.mm"
include "sumeq1d.mm"
include "3eqtr4a.mm"
include "jaoi.mm"
include "sylbi.mm"

theorem logfac
  let vk: setvar k
  let cN: class N
  let vn: setvar n
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B

  disjoint N k
  disjoint n x
  disjoint n y
  disjoint A n
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint B n
  disjoint B y
  disjoint k n
  disjoint N n
  assert |- ( N e. NN0 -> ( log ` ( ! ` N ) ) = sum_ k e. ( 1 ... N ) ( log ` k ) )

  proof
    cN
    cn0
    wcel
    cN
    cn
    wcel
    #
    cN
    cc0
    wceq
    #
    wo
    cN
    cfa
    cfv
    #
    clog
    cfv
    #
    c1
    cN
    cfz
    co
    #
    vk
    cv
    #
    clog
    cfv
    #
    vk
    csu
    #
    wceq
    #
    cN
    elnn0
    @0
    @8
    @1
    @0
    cN
    cmul
    cid
    c1
    cseq
    cfv
    #
    clog
    cfv
    cN
    caddc
    clog
    c1
    cseq
    cfv
    @3
    @7
    @0
    vk
    vn
    cmul
    caddc
    crp
    cid
    clog
    clog
    c1
    cN
    @5
    crp
    wcel
    #
    vn
    cv
    #
    crp
    wcel
    wa
    #
    @5
    @11
    cmul
    co
    #
    crp
    wcel
    @0
    @5
    @11
    rpmulcl
    adantl
    @0
    @5
    @4
    wcel
    #
    wa
    #
    @5
    cid
    cfv
    #
    @5
    crp
    @5
    cvv
    wcel
    @16
    @5
    wceq
    vk
    vex
    @5
    cvv
    fvi
    ax-mp
    #
    @15
    @5
    @14
    @5
    cn
    wcel
    @0
    @5
    cN
    elfznn
    adantl
    nnrpd
    #
    syl5eqel
    @0
    cN
    c1
    cuz
    cfv
    wcel
    cN
    elnnuz
    biimpi
    #
    @12
    @13
    clog
    cfv
    @6
    @11
    clog
    cfv
    caddc
    co
    wceq
    @0
    @5
    @11
    relogmul
    adantl
    @16
    clog
    cfv
    @6
    wceq
    @15
    @16
    @5
    clog
    @17
    fveq2i
    a1i
    seqhomo
    @0
    @2
    @9
    clog
    cN
    facnn
    fveq2d
    @0
    @6
    vk
    clog
    c1
    cN
    @15
    @6
    eqidd
    @19
    @15
    @6
    @15
    @10
    @6
    cr
    wcel
    @18
    @5
    relogcl
    syl
    recnd
    fsumser
    3eqtr4d
    @1
    c1
    clog
    cfv
    #
    c0
    @6
    vk
    csu
    #
    @3
    @7
    @20
    cc0
    @21
    log1
    @6
    vk
    sum0
    eqtr4i
    @1
    @2
    c1
    clog
    @1
    @2
    cc0
    cfa
    cfv
    c1
    cN
    cc0
    cfa
    fveq2
    fac0
    syl6eq
    fveq2d
    @1
    @4
    c0
    @6
    vk
    @1
    @4
    c1
    cc0
    cfz
    co
    c0
    cN
    cc0
    c1
    cfz
    oveq2
    fz10
    syl6eq
    sumeq1d
    3eqtr4a
    jaoi
    sylbi
end
