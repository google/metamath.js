include "cz.mm"
include "wcel.mm"
include "cn.mm"
include "wa.mm"
include "cmo.mm"
include "co.mm"
include "cc0.mm"
include "wne.mm"
include "cv.mm"
include "cmul.mm"
include "caddc.mm"
include "wceq.mm"
include "c1.mm"
include "cfzo.mm"
include "wrex.mm"
include "cdiv.mm"
include "cfl.mm"
include "cfv.mm"
include "cr.mm"
include "zre.mm"
include "adantr.mm"
include "nnre.mm"
include "adantl.mm"
include "nnne0.mm"
include "redivcld.mm"
include "flcld.mm"
include "zmodfzo.mm"
include "anim1i.mm"
include "fzo1fzo0n0.mm"
include "sylibr.mm"
include "crp.mm"
include "nnrp.mm"
include "anim12i.mm"
include "flpmodeq.mm"
include "syl.mm"
include "eqcomd.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "eqeq2d.mm"
include "oveq2.mm"
include "rspc2ev.mm"
include "syl3anc.mm"
include "ex.mm"

theorem modn0mul
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cN: class N
  let vk: setvar k

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint N x
  disjoint N y
  disjoint k x
  assert |- ( ( A e. ZZ /\ N e. NN ) -> ( ( A mod N ) =/= 0 -> E. x e. ZZ E. y e. ( 1 ..^ N ) A = ( ( x x. N ) + y ) ) )

  proof
    cA
    cz
    wcel
    #
    cN
    cn
    wcel
    #
    wa
    #
    cA
    cN
    cmo
    co
    #
    cc0
    wne
    #
    cA
    vx
    cv
    #
    cN
    cmul
    co
    #
    vy
    cv
    #
    caddc
    co
    #
    wceq
    #
    vy
    c1
    cN
    cfzo
    co
    #
    wrex
    vx
    cz
    wrex
    #
    @2
    @4
    wa
    #
    cA
    cN
    cdiv
    co
    #
    cfl
    cfv
    #
    cz
    wcel
    #
    @3
    @10
    wcel
    #
    cA
    @14
    cN
    cmul
    co
    #
    @3
    caddc
    co
    #
    wceq
    #
    @11
    @2
    @15
    @4
    @2
    @13
    @2
    cA
    cN
    @0
    cA
    cr
    wcel
    #
    @1
    cA
    zre
    #
    adantr
    @1
    cN
    cr
    wcel
    @0
    cN
    nnre
    adantl
    @1
    cN
    cc0
    wne
    @0
    cN
    nnne0
    adantl
    redivcld
    flcld
    adantr
    @12
    @3
    cc0
    cN
    cfzo
    co
    wcel
    #
    @4
    wa
    @16
    @2
    @22
    @4
    cA
    cN
    zmodfzo
    anim1i
    @3
    cN
    fzo1fzo0n0
    sylibr
    @12
    @18
    cA
    @12
    @20
    cN
    crp
    wcel
    #
    wa
    #
    @18
    cA
    wceq
    @2
    @24
    @4
    @0
    @20
    @1
    @23
    @21
    cN
    nnrp
    anim12i
    adantr
    cA
    cN
    flpmodeq
    syl
    eqcomd
    @9
    @19
    cA
    @17
    @7
    caddc
    co
    #
    wceq
    vx
    vy
    @14
    @3
    cz
    @10
    @5
    @14
    wceq
    #
    @8
    @25
    cA
    @26
    @6
    @17
    @7
    caddc
    @5
    @14
    cN
    cmul
    oveq1
    oveq1d
    eqeq2d
    @7
    @3
    wceq
    @25
    @18
    cA
    @7
    @3
    @17
    caddc
    oveq2
    eqeq2d
    rspc2ev
    syl3anc
    ex
end
