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
include "ccnv.mm"
include "cima.mm"
include "eulerpartlemsv1.mm"
include "c1.mm"
include "cdm.mm"
include "cnvimass.mm"
include "wf.mm"
include "wceq.mm"
include "cfn.mm"
include "eulerpartlemelr.mm"
include "simpld.mm"
include "fdm.mm"
include "syl.mm"
include "syl5sseq.mm"
include "wa.mm"
include "adantr.mm"
include "sselda.mm"
include "ffvelrnd.mm"
include "nnnn0d.mm"
include "nn0mulcld.mm"
include "nn0cnd.mm"
include "cdif.mm"
include "cc0.mm"
include "wn.mm"
include "wo.mm"
include "simpr.mm"
include "eldifad.mm"
include "wi.mm"
include "eldifbd.mm"
include "wfn.mm"
include "wb.mm"
include "ffn.mm"
include "elpreima.mm"
include "3syl.mm"
include "mtbid.mm"
include "imnan.mm"
include "sylibr.mm"
include "mpd.mm"
include "elnn0.mm"
include "sylib.mm"
include "orel1.mm"
include "sylc.mm"
include "oveq1d.mm"
include "nncnd.mm"
include "mul02d.mm"
include "eqtrd.mm"
include "cuz.mm"
include "wss.mm"
include "nnuz.mm"
include "eqimssi.mm"
include "a1i.mm"
include "sumss.mm"
include "eqtr4d.mm"

theorem eulerpartlemsv2
  let cA: class A
  let cR: class R
  let cS: class S
  let vf: setvar f
  let vk: setvar k
  assume eulerpartlems.r: |- R = { f | ( `' f " NN ) e. Fin }
  assume eulerpartlems.s: |- S = ( f e. ( ( NN0 ^m NN ) i^i R ) |-> sum_ k e. NN ( ( f ` k ) x. k ) )

  disjoint f k
  disjoint A f
  disjoint A k
  disjoint R f
  disjoint R k
  assert |- ( A e. ( ( NN0 ^m NN ) i^i R ) -> ( S ` A ) = sum_ k e. ( `' A " NN ) ( ( A ` k ) x. k ) )

  proof
    cA
    cn0
    cn
    cmap
    co
    cR
    cin
    wcel
    #
    cA
    cS
    cfv
    cn
    vk
    cv
    #
    cA
    cfv
    #
    @1
    cmul
    co
    #
    vk
    csu
    cA
    ccnv
    cn
    cima
    #
    @3
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
    @0
    @4
    cn
    @3
    vk
    c1
    @0
    cA
    cdm
    #
    @4
    cn
    cA
    cn
    cnvimass
    @0
    cn
    cn0
    cA
    wf
    #
    @5
    cn
    wceq
    @0
    @6
    @4
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
    #
    cn
    cn0
    cA
    fdm
    syl
    syl5sseq
    #
    @0
    @1
    @4
    wcel
    #
    wa
    #
    @3
    @10
    @2
    @1
    @10
    cn
    cn0
    @1
    cA
    @0
    @6
    @9
    @7
    adantr
    @0
    @4
    cn
    @1
    @8
    sselda
    #
    ffvelrnd
    @10
    @1
    @11
    nnnn0d
    nn0mulcld
    nn0cnd
    @0
    @1
    cn
    @4
    cdif
    wcel
    #
    wa
    #
    @3
    cc0
    @1
    cmul
    co
    cc0
    @13
    @2
    cc0
    @1
    cmul
    @13
    @2
    cn
    wcel
    #
    wn
    #
    @14
    @2
    cc0
    wceq
    #
    wo
    #
    @16
    @13
    @1
    cn
    wcel
    #
    @15
    @13
    @1
    cn
    @4
    @0
    @12
    simpr
    #
    eldifad
    #
    @13
    @18
    @14
    wa
    #
    wn
    @18
    @15
    wi
    @13
    @9
    @21
    @13
    @1
    cn
    @4
    @19
    eldifbd
    @13
    @6
    cA
    cn
    wfn
    @9
    @21
    wb
    @0
    @6
    @12
    @7
    adantr
    #
    cn
    cn0
    cA
    ffn
    cn
    @1
    cn
    cA
    elpreima
    3syl
    mtbid
    @18
    @14
    imnan
    sylibr
    mpd
    @13
    @2
    cn0
    wcel
    @17
    @13
    cn
    cn0
    @1
    cA
    @22
    @20
    ffvelrnd
    @2
    elnn0
    sylib
    @14
    @16
    orel1
    sylc
    oveq1d
    @13
    @1
    @13
    @1
    @20
    nncnd
    mul02d
    eqtrd
    cn
    c1
    cuz
    cfv
    #
    wss
    @0
    cn
    @23
    nnuz
    eqimssi
    a1i
    sumss
    eqtr4d
end
