include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "co.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt2.mm"
include "cii.mm"
include "ctx.mm"
include "ccn.mm"
include "ctopon.mm"
include "wcel.mm"
include "iitopon.mm"
include "a1i.mm"
include "cnmpt1st.mm"
include "cnmpt21f.mm"
include "syl5eqel.mm"
include "wa.mm"
include "wceq.mm"
include "simpr.mm"
include "0elunit.mm"
include "fveq2.mm"
include "eqidd.mm"
include "fvex.mm"
include "ovmpt2.mm"
include "sylancl.mm"
include "1elunit.mm"
include "ishtpyd.mm"

theorem htpyid
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  let cG: class G
  let cJ: class J
  let cK: class K
  let cX: class X
  let vs: setvar s
  assume htpyid.1: |- G = ( x e. X , y e. ( 0 [,] 1 ) |-> ( F ` x ) )
  assume htpyid.2: |- ( ph -> J e. ( TopOn ` X ) )
  assume htpyid.4: |- ( ph -> F e. ( J Cn K ) )

  disjoint x y
  disjoint F x
  disjoint F y
  disjoint J x
  disjoint J y
  disjoint K x
  disjoint K y
  disjoint ph x
  disjoint ph y
  disjoint X x
  disjoint X y
  disjoint s x
  disjoint s y
  disjoint F s
  disjoint J s
  disjoint ph s
  disjoint X s
  disjoint G s
  assert |- ( ph -> G e. ( F ( J Htpy K ) F ) )

  proof
    wph
    cF
    cF
    cG
    cJ
    cK
    cX
    vs
    htpyid.2
    htpyid.4
    htpyid.4
    wph
    cG
    vx
    vy
    cX
    cc0
    c1
    cicc
    co
    #
    vx
    cv
    #
    cF
    cfv
    #
    cmpt2
    cJ
    cii
    ctx
    co
    cK
    ccn
    co
    htpyid.1
    wph
    vx
    vy
    @1
    cF
    cJ
    cii
    cJ
    cK
    cX
    @0
    htpyid.2
    cii
    @0
    ctopon
    cfv
    wcel
    wph
    iitopon
    a1i
    #
    wph
    vx
    vy
    cJ
    cii
    cX
    @0
    htpyid.2
    @3
    cnmpt1st
    htpyid.4
    cnmpt21f
    syl5eqel
    wph
    vs
    cv
    #
    cX
    wcel
    #
    wa
    #
    @5
    cc0
    @0
    wcel
    @4
    cc0
    cG
    co
    @4
    cF
    cfv
    #
    wceq
    wph
    @5
    simpr
    #
    0elunit
    vx
    vy
    @4
    cc0
    cX
    @0
    @2
    @7
    cG
    @7
    @1
    @4
    cF
    fveq2
    #
    vy
    cv
    #
    cc0
    wceq
    @7
    eqidd
    htpyid.1
    @4
    cF
    fvex
    #
    ovmpt2
    sylancl
    @6
    @5
    c1
    @0
    wcel
    @4
    c1
    cG
    co
    @7
    wceq
    @8
    1elunit
    vx
    vy
    @4
    c1
    cX
    @0
    @2
    @7
    cG
    @7
    @9
    @10
    c1
    wceq
    @7
    eqidd
    htpyid.1
    @11
    ovmpt2
    sylancl
    ishtpyd
end
