include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "co.mm"
include "wrex.mm"
include "cxp.mm"
include "wcel.mm"
include "wa.mm"
include "cop.mm"
include "simp-4r.mm"
include "simpr.mm"
include "fveq2d.mm"
include "eqtr3d.mm"
include "df-ov.mm"
include "syl6eqr.mm"
include "simplr.mm"
include "elxp2.mm"
include "sylib.mm"
include "reximddv2.mm"
include "wfun.mm"
include "cima.mm"
include "syl6eleq.mm"
include "fvelima.mm"
include "syl2anc.mm"
include "r19.29a.mm"

theorem ltgseg
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cP: class P
  let cE: class E
  let cG: class G
  let cI: class I
  let c.le: class .<_
  let c.mi: class .-
  let va: setvar a
  assume legval.p: |- P = ( Base ` G )
  assume legval.d: |- .- = ( dist ` G )
  assume legval.i: |- I = ( Itv ` G )
  assume legval.l: |- .<_ = ( leG ` G )
  assume legval.g: |- ( ph -> G e. TarskiG )
  assume legso.a: |- E = ( .- " ( P X. P ) )
  assume legso.f: |- ( ph -> Fun .- )
  assume ltgseg.p: |- ( ph -> A e. E )

  disjoint .- x
  disjoint .- y
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint P x
  disjoint P y
  disjoint ph x
  disjoint ph y
  disjoint .- a
  disjoint a x
  disjoint a y
  disjoint A a
  disjoint P a
  disjoint a ph
  assert |- ( ph -> E. x e. P E. y e. P A = ( x .- y ) )

  proof
    wph
    va
    cv
    #
    c.mi
    cfv
    #
    cA
    wceq
    #
    cA
    vx
    cv
    #
    vy
    cv
    #
    c.mi
    co
    #
    wceq
    #
    vy
    cP
    wrex
    vx
    cP
    wrex
    va
    cP
    cP
    cxp
    #
    wph
    @0
    @7
    wcel
    #
    wa
    #
    @2
    wa
    #
    @0
    @3
    @4
    cop
    #
    wceq
    #
    @6
    vx
    vy
    cP
    cP
    @10
    @3
    cP
    wcel
    #
    wa
    @4
    cP
    wcel
    #
    wa
    #
    @12
    wa
    #
    cA
    @11
    c.mi
    cfv
    #
    @5
    @16
    @1
    cA
    @17
    @9
    @2
    @13
    @14
    @12
    simp-4r
    @16
    @0
    @11
    c.mi
    @15
    @12
    simpr
    fveq2d
    eqtr3d
    @3
    @4
    c.mi
    df-ov
    syl6eqr
    @10
    @8
    @12
    vy
    cP
    wrex
    vx
    cP
    wrex
    wph
    @8
    @2
    simplr
    vx
    vy
    @0
    cP
    cP
    elxp2
    sylib
    reximddv2
    wph
    c.mi
    wfun
    cA
    c.mi
    @7
    cima
    #
    wcel
    @2
    va
    @7
    wrex
    legso.f
    wph
    cA
    cE
    @18
    ltgseg.p
    legso.a
    syl6eleq
    va
    cA
    @7
    c.mi
    fvelima
    syl2anc
    r19.29a
end
