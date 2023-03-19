include "crp.mm"
include "wcel.mm"
include "cc.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cuz.mm"
include "wral.mm"
include "wrex.mm"
include "cli.mm"
include "cvv.mm"
include "wrel.mm"
include "climrel.mm"
include "a1i.mm"
include "brrelex.mm"
include "syl2anc.mm"
include "clim2f2.mm"
include "mpbid.mm"
include "simprd.mm"
include "wceq.mm"
include "breq2.mm"
include "anbi2d.mm"
include "ralbidv.mm"
include "rexbidv.mm"
include "rspcva.mm"

theorem clim2d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cX: class X
  let cZ: class Z
  let vx: setvar x
  assume clim2d.k: |- F/ k ph
  assume clim2d.f: |- F/_ k F
  assume clim2d.m: |- ( ph -> M e. ZZ )
  assume clim2d.z: |- Z = ( ZZ>= ` M )
  assume clim2d.c: |- ( ph -> F ~~> A )
  assume clim2d.b: |- ( ( ph /\ k e. Z ) -> ( F ` k ) = B )
  assume clim2d.x: |- ( ph -> X e. RR+ )

  disjoint A j
  disjoint A k
  disjoint j k
  disjoint F j
  disjoint M j
  disjoint X j
  disjoint X k
  disjoint Z j
  disjoint Z k
  disjoint j ph
  disjoint A x
  disjoint j x
  disjoint k x
  disjoint B x
  disjoint F x
  disjoint X x
  disjoint Z x
  disjoint ph x
  assert |- ( ph -> E. j e. Z A. k e. ( ZZ>= ` j ) ( B e. CC /\ ( abs ` ( B - A ) ) < X ) )

  proof
    wph
    cX
    crp
    wcel
    cB
    cc
    wcel
    #
    cB
    cA
    cmin
    co
    cabs
    cfv
    #
    vx
    cv
    #
    clt
    wbr
    #
    wa
    #
    vk
    vj
    cv
    cuz
    cfv
    #
    wral
    #
    vj
    cZ
    wrex
    #
    vx
    crp
    wral
    #
    @0
    @1
    cX
    clt
    wbr
    #
    wa
    #
    vk
    @5
    wral
    #
    vj
    cZ
    wrex
    #
    clim2d.x
    wph
    cA
    cc
    wcel
    #
    @8
    wph
    cF
    cA
    cli
    wbr
    #
    @13
    @8
    wa
    clim2d.c
    wph
    vx
    cA
    cB
    vj
    vk
    cF
    cM
    cvv
    cZ
    clim2d.k
    clim2d.f
    clim2d.z
    clim2d.m
    wph
    cli
    wrel
    #
    @14
    cF
    cvv
    wcel
    @15
    wph
    climrel
    a1i
    clim2d.c
    cF
    cA
    cli
    brrelex
    syl2anc
    clim2d.b
    clim2f2
    mpbid
    simprd
    @7
    @12
    vx
    cX
    crp
    @2
    cX
    wceq
    #
    @6
    @11
    vj
    cZ
    @16
    @4
    @10
    vk
    @5
    @16
    @3
    @9
    @0
    @2
    cX
    @1
    clt
    breq2
    anbi2d
    ralbidv
    rexbidv
    rspcva
    syl2anc
end
