include "cn0.mm"
include "cn.mm"
include "cmap.mm"
include "co.mm"
include "cin.mm"
include "wcel.mm"
include "cfv.mm"
include "cv.mm"
include "cmul.mm"
include "csu.mm"
include "c1.mm"
include "cfz.mm"
include "eulerpartlemsv1.mm"
include "wss.mm"
include "cuz.mm"
include "fzssuz.mm"
include "nnuz.mm"
include "sseqtr4i.mm"
include "a1i.mm"
include "wa.mm"
include "wf.mm"
include "ccnv.mm"
include "cima.mm"
include "cfn.mm"
include "eulerpartlemelr.mm"
include "simpld.mm"
include "adantr.mm"
include "sselda.mm"
include "ffvelrnd.mm"
include "nn0cnd.mm"
include "nncnd.mm"
include "mulcld.mm"
include "cdif.mm"
include "cc0.mm"
include "wceq.mm"
include "wral.mm"
include "caddc.mm"
include "eulerpartlems.mm"
include "ralrimiva.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "cbvralv.mm"
include "sylibr.mm"
include "eulerpartlemsf.mm"
include "ffvelrni.mm"
include "nndiffz1.mm"
include "syl.mm"
include "raleqdv.mm"
include "mpbird.mm"
include "r19.21bi.mm"
include "oveq1d.mm"
include "simpr.mm"
include "eldifad.mm"
include "mul02d.mm"
include "eqtrd.mm"
include "eqimssi.mm"
include "sumss.mm"
include "eqtr4d.mm"

theorem eulerpartlemsv3
  let cA: class A
  let cR: class R
  let cS: class S
  let vf: setvar f
  let vk: setvar k
  let vg: setvar g
  let vl: setvar l
  let vm: setvar m
  let vt: setvar t
  assume eulerpartlems.r: |- R = { f | ( `' f " NN ) e. Fin }
  assume eulerpartlems.s: |- S = ( f e. ( ( NN0 ^m NN ) i^i R ) |-> sum_ k e. NN ( ( f ` k ) x. k ) )

  disjoint f k
  disjoint A f
  disjoint A k
  disjoint R f
  disjoint R k
  disjoint S k
  disjoint f g
  disjoint g k
  disjoint R g
  disjoint k l
  disjoint k m
  disjoint k t
  disjoint l m
  disjoint l t
  disjoint A l
  disjoint m t
  disjoint A m
  disjoint A t
  disjoint R l
  disjoint R t
  disjoint S l
  disjoint S t
  assert |- ( A e. ( ( NN0 ^m NN ) i^i R ) -> ( S ` A ) = sum_ k e. ( 1 ... ( S ` A ) ) ( ( A ` k ) x. k ) )

  proof
    cA
    cn0
    cn
    cmap
    co
    cR
    cin
    #
    wcel
    #
    cA
    cS
    cfv
    #
    cn
    vk
    cv
    #
    cA
    cfv
    #
    @3
    cmul
    co
    #
    vk
    csu
    c1
    @2
    cfz
    co
    #
    @5
    vk
    csu
    cA
    cR
    cS
    vf
    vk
    eulerpartlems.r
    eulerpartlems.s
    eulerpartlemsv1
    @1
    @6
    cn
    @5
    vk
    c1
    @6
    cn
    wss
    @1
    @6
    c1
    cuz
    cfv
    #
    cn
    c1
    @2
    fzssuz
    nnuz
    sseqtr4i
    a1i
    #
    @1
    @3
    @6
    wcel
    #
    wa
    #
    @4
    @3
    @10
    @4
    @10
    cn
    cn0
    @3
    cA
    @1
    cn
    cn0
    cA
    wf
    #
    @9
    @1
    @11
    cA
    ccnv
    cn
    cima
    cfn
    wcel
    cA
    cR
    cS
    vf
    vk
    eulerpartlems.r
    eulerpartlems.s
    eulerpartlemelr
    simpld
    adantr
    @1
    @6
    cn
    @3
    @8
    sselda
    #
    ffvelrnd
    nn0cnd
    @10
    @3
    @12
    nncnd
    mulcld
    @1
    @3
    cn
    @6
    cdif
    #
    wcel
    #
    wa
    #
    @5
    cc0
    @3
    cmul
    co
    cc0
    @15
    @4
    cc0
    @3
    cmul
    @1
    @4
    cc0
    wceq
    #
    vk
    @13
    @1
    @16
    vk
    @13
    wral
    @16
    vk
    @2
    c1
    caddc
    co
    cuz
    cfv
    #
    wral
    #
    @1
    vt
    cv
    #
    cA
    cfv
    #
    cc0
    wceq
    #
    vt
    @17
    wral
    @18
    @1
    @21
    vt
    @17
    vt
    cA
    cR
    cS
    vf
    vk
    eulerpartlems.r
    eulerpartlems.s
    eulerpartlems
    ralrimiva
    @16
    @21
    vk
    vt
    @17
    @3
    @19
    wceq
    @4
    @20
    cc0
    @3
    @19
    cA
    fveq2
    eqeq1d
    cbvralv
    sylibr
    @1
    @16
    vk
    @13
    @17
    @1
    @2
    cn0
    wcel
    @13
    @17
    wceq
    @0
    cn0
    cA
    cS
    cR
    cS
    vf
    vk
    eulerpartlems.r
    eulerpartlems.s
    eulerpartlemsf
    ffvelrni
    @2
    nndiffz1
    syl
    raleqdv
    mpbird
    r19.21bi
    oveq1d
    @15
    @3
    @15
    @3
    @15
    @3
    cn
    @6
    @1
    @14
    simpr
    eldifad
    nncnd
    mul02d
    eqtrd
    cn
    @7
    wss
    @1
    cn
    @7
    nnuz
    eqimssi
    a1i
    sumss
    eqtr4d
end
