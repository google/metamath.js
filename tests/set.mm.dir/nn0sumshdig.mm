include "cn0.mm"
include "wcel.mm"
include "cblen.mm"
include "cfv.mm"
include "cn.mm"
include "cc0.mm"
include "cfzo.mm"
include "co.mm"
include "cv.mm"
include "c2.mm"
include "cdig.mm"
include "cexp.mm"
include "cmul.mm"
include "csu.mm"
include "wceq.mm"
include "blennn0elnn.mm"
include "wi.mm"
include "wral.mm"
include "nn0sumshdiglem2.mm"
include "wa.mm"
include "eqid.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "id.mm"
include "oveq2.mm"
include "oveq1d.mm"
include "adantr.mm"
include "sumeq2dv.mm"
include "eqeq12d.mm"
include "imbi12d.mm"
include "rspcva.mm"
include "mpi.mm"
include "ex.mm"
include "syl5.mm"
include "mpd.mm"

theorem nn0sumshdig
  let cA: class A
  let vk: setvar k
  let va: setvar a
  let vi: setvar i
  let vx: setvar x
  let vy: setvar y
  let cL: class L

  disjoint A k
  disjoint a i
  disjoint a k
  disjoint a x
  disjoint a y
  disjoint i k
  disjoint i x
  disjoint i y
  disjoint k x
  disjoint k y
  disjoint x y
  disjoint L a
  disjoint L k
  disjoint L x
  disjoint L y
  disjoint A a
  disjoint k x
  assert |- ( A e. NN0 -> A = sum_ k e. ( 0 ..^ ( #b ` A ) ) ( ( k ( digit ` 2 ) A ) x. ( 2 ^ k ) ) )

  proof
    cA
    cn0
    wcel
    #
    cA
    cblen
    cfv
    #
    cn
    wcel
    #
    cA
    cc0
    @1
    cfzo
    co
    #
    vk
    cv
    #
    cA
    c2
    cdig
    cfv
    #
    co
    #
    c2
    @4
    cexp
    co
    #
    cmul
    co
    #
    vk
    csu
    #
    wceq
    #
    cA
    blennn0elnn
    @2
    va
    cv
    #
    cblen
    cfv
    #
    @1
    wceq
    #
    @11
    @3
    @4
    @11
    @5
    co
    #
    @7
    cmul
    co
    #
    vk
    csu
    #
    wceq
    #
    wi
    #
    va
    cn0
    wral
    #
    @0
    @10
    vk
    @1
    va
    nn0sumshdiglem2
    @0
    @19
    @10
    @0
    @19
    wa
    @1
    @1
    wceq
    #
    @10
    @1
    eqid
    @18
    @20
    @10
    wi
    va
    cA
    cn0
    @11
    cA
    wceq
    #
    @13
    @20
    @17
    @10
    @21
    @12
    @1
    @1
    @11
    cA
    cblen
    fveq2
    eqeq1d
    @21
    @11
    cA
    @16
    @9
    @21
    id
    @21
    @3
    @15
    @8
    vk
    @21
    @15
    @8
    wceq
    @4
    @3
    wcel
    @21
    @14
    @6
    @7
    cmul
    @11
    cA
    @4
    @5
    oveq2
    oveq1d
    adantr
    sumeq2dv
    eqeq12d
    imbi12d
    rspcva
    mpi
    ex
    syl5
    mpd
end
