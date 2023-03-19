include "cc.mm"
include "wcel.mm"
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
include "crp.mm"
include "cli.mm"
include "biantrurd.mm"
include "wb.mm"
include "uztrn2.mm"
include "sylan2.mm"
include "anassrs.mm"
include "ralbidva.mm"
include "rexbidva.mm"
include "ralbidv.mm"
include "clim2f.mm"
include "3bitr4rd.mm"

theorem clim2cf
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cV: class V
  let cZ: class Z
  assume clim2cf.nf: |- F/_ k F
  assume clim2cf.z: |- Z = ( ZZ>= ` M )
  assume clim2cf.m: |- ( ph -> M e. ZZ )
  assume clim2cf.f: |- ( ph -> F e. V )
  assume clim2cf.fv: |- ( ( ph /\ k e. Z ) -> ( F ` k ) = B )
  assume clim2cf.a: |- ( ph -> A e. CC )
  assume clim2cf.b: |- ( ( ph /\ k e. Z ) -> B e. CC )

  disjoint A j
  disjoint A k
  disjoint A x
  disjoint j k
  disjoint j x
  disjoint k x
  disjoint F j
  disjoint F x
  disjoint M j
  disjoint Z j
  disjoint Z k
  disjoint j ph
  disjoint k ph
  disjoint ph x
  assert |- ( ph -> ( F ~~> A <-> A. x e. RR+ E. j e. Z A. k e. ( ZZ>= ` j ) ( abs ` ( B - A ) ) < x ) )

  proof
    wph
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
    vx
    cv
    clt
    wbr
    #
    wa
    #
    vk
    vj
    cv
    #
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
    cA
    cc
    wcel
    #
    @7
    wa
    @1
    vk
    @4
    wral
    #
    vj
    cZ
    wrex
    #
    vx
    crp
    wral
    cF
    cA
    cli
    wbr
    wph
    @8
    @7
    clim2cf.a
    biantrurd
    wph
    @10
    @6
    vx
    crp
    wph
    @9
    @5
    vj
    cZ
    wph
    @3
    cZ
    wcel
    #
    wa
    @1
    @2
    vk
    @4
    wph
    @11
    vk
    cv
    #
    @4
    wcel
    #
    @1
    @2
    wb
    #
    @11
    @13
    wa
    wph
    @12
    cZ
    wcel
    #
    @14
    cM
    @12
    @3
    cZ
    clim2cf.z
    uztrn2
    wph
    @15
    wa
    @0
    @1
    clim2cf.b
    biantrurd
    sylan2
    anassrs
    ralbidva
    rexbidva
    ralbidv
    wph
    vx
    cA
    cB
    vj
    vk
    cF
    cM
    cV
    cZ
    clim2cf.nf
    clim2cf.z
    clim2cf.m
    clim2cf.f
    clim2cf.fv
    clim2f
    3bitr4rd
end
