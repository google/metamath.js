include "cn0.mm"
include "cn.mm"
include "cmap.mm"
include "co.mm"
include "cin.mm"
include "cv.mm"
include "cfv.mm"
include "cmul.mm"
include "csu.mm"
include "wcel.mm"
include "wceq.mm"
include "wa.mm"
include "simpl.mm"
include "fveq1d.mm"
include "oveq1d.mm"
include "sumeq2dv.mm"
include "eleq1d.mm"
include "ccnv.mm"
include "cima.mm"
include "eulerpartlemsv2.mm"
include "eulerpartlemsv1.mm"
include "eqtr3d.mm"
include "wf.mm"
include "cfn.mm"
include "eulerpartlemelr.mm"
include "simprd.mm"
include "simpld.mm"
include "adantr.mm"
include "cdm.mm"
include "cnvimass.mm"
include "fdm.mm"
include "syl.mm"
include "syl5sseq.mm"
include "sselda.mm"
include "ffvelrnd.mm"
include "nnnn0d.mm"
include "nn0mulcld.mm"
include "fsumnn0cl.mm"
include "eqeltrrd.mm"
include "vtoclga.mm"
include "fmpti.mm"

theorem eulerpartlemsf
  let cR: class R
  let cS: class S
  let vf: setvar f
  let vk: setvar k
  let cA: class A
  let vg: setvar g
  assume eulerpartlems.r: |- R = { f | ( `' f " NN ) e. Fin }
  assume eulerpartlems.s: |- S = ( f e. ( ( NN0 ^m NN ) i^i R ) |-> sum_ k e. NN ( ( f ` k ) x. k ) )

  disjoint f k
  disjoint R f
  disjoint R k
  disjoint A f
  disjoint A k
  disjoint f g
  disjoint g k
  disjoint R g
  assert |- S : ( ( NN0 ^m NN ) i^i R ) --> NN0

  proof
    vf
    cn0
    cn
    cmap
    co
    cR
    cin
    #
    cn0
    cn
    vk
    cv
    #
    vf
    cv
    #
    cfv
    #
    @1
    cmul
    co
    #
    vk
    csu
    #
    cS
    eulerpartlems.s
    cn
    @1
    vg
    cv
    #
    cfv
    #
    @1
    cmul
    co
    #
    vk
    csu
    #
    cn0
    wcel
    @5
    cn0
    wcel
    vg
    @2
    @0
    @6
    @2
    wceq
    #
    @9
    @5
    cn0
    @10
    cn
    @8
    @4
    vk
    @10
    @1
    cn
    wcel
    #
    wa
    #
    @7
    @3
    @1
    cmul
    @12
    @1
    @6
    @2
    @10
    @11
    simpl
    fveq1d
    oveq1d
    sumeq2dv
    eleq1d
    @6
    @0
    wcel
    #
    @6
    ccnv
    cn
    cima
    #
    @8
    vk
    csu
    #
    @9
    cn0
    @13
    @6
    cS
    cfv
    @15
    @9
    @6
    cR
    cS
    vf
    vk
    eulerpartlems.r
    eulerpartlems.s
    eulerpartlemsv2
    @6
    cR
    cS
    vf
    vk
    eulerpartlems.r
    eulerpartlems.s
    eulerpartlemsv1
    eqtr3d
    @13
    @14
    @8
    vk
    @13
    cn
    cn0
    @6
    wf
    #
    @14
    cfn
    wcel
    #
    @6
    cR
    cS
    vf
    vk
    eulerpartlems.r
    eulerpartlems.s
    eulerpartlemelr
    #
    simprd
    @13
    @1
    @14
    wcel
    #
    wa
    #
    @7
    @1
    @20
    cn
    cn0
    @1
    @6
    @13
    @16
    @19
    @13
    @16
    @17
    @18
    simpld
    #
    adantr
    @13
    @14
    cn
    @1
    @13
    @6
    cdm
    #
    @14
    cn
    @6
    cn
    cnvimass
    @13
    @16
    @22
    cn
    wceq
    @21
    cn
    cn0
    @6
    fdm
    syl
    syl5sseq
    sselda
    #
    ffvelrnd
    @20
    @1
    @23
    nnnn0d
    nn0mulcld
    fsumnn0cl
    eqeltrrd
    vtoclga
    fmpti
end
