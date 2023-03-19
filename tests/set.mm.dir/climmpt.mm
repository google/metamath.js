include "cz.mm"
include "wcel.mm"
include "wa.mm"
include "cvv.mm"
include "simpr.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "cuz.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptex.mm"
include "a1i.mm"
include "simpl.mm"
include "wceq.mm"
include "fveq2.mm"
include "fvmpt.mm"
include "eqcomd.mm"
include "adantl.mm"
include "climeq.mm"

theorem climmpt
  let cA: class A
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cM: class M
  let cV: class V
  let cZ: class Z
  let vj: setvar j
  let vm: setvar m
  let vy: setvar y
  let vx: setvar x
  let wph: wff ph
  assume 2clim.1: |- Z = ( ZZ>= ` M )
  assume climmpt.2: |- G = ( k e. Z |-> ( F ` k ) )

  disjoint A k
  disjoint F k
  disjoint Z k
  disjoint j k
  disjoint j m
  disjoint j y
  disjoint A j
  disjoint k m
  disjoint k y
  disjoint m y
  disjoint A m
  disjoint A y
  disjoint j x
  disjoint F j
  disjoint k x
  disjoint m x
  disjoint F m
  disjoint F x
  disjoint G j
  disjoint G m
  disjoint x y
  disjoint G x
  disjoint G y
  disjoint M j
  disjoint M m
  disjoint V m
  disjoint j ph
  disjoint k ph
  disjoint ph y
  disjoint Z j
  disjoint Z m
  disjoint Z x
  assert |- ( ( M e. ZZ /\ F e. V ) -> ( F ~~> A <-> G ~~> A ) )

  proof
    cM
    cz
    wcel
    #
    cF
    cV
    wcel
    #
    wa
    #
    cA
    vm
    cF
    cG
    cM
    cV
    cvv
    cZ
    2clim.1
    @0
    @1
    simpr
    cG
    cvv
    wcel
    @2
    cG
    vk
    cZ
    vk
    cv
    #
    cF
    cfv
    #
    cmpt
    cvv
    climmpt.2
    vk
    cZ
    @4
    cZ
    cM
    cuz
    cfv
    cvv
    2clim.1
    cM
    cuz
    fvex
    eqeltri
    mptex
    eqeltri
    a1i
    @0
    @1
    simpl
    vm
    cv
    #
    cZ
    wcel
    #
    @5
    cF
    cfv
    #
    @5
    cG
    cfv
    #
    wceq
    @2
    @6
    @8
    @7
    vk
    @5
    @4
    @7
    cZ
    cG
    @3
    @5
    cF
    fveq2
    climmpt.2
    @5
    cF
    fvex
    fvmpt
    eqcomd
    adantl
    climeq
end
