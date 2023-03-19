include "cc0.mm"
include "cv.mm"
include "co.mm"
include "cfv.mm"
include "wceq.mm"
include "c1.mm"
include "wa.mm"
include "cicc.mm"
include "wral.mm"
include "wcel.mm"
include "cii.mm"
include "chtpy.mm"
include "cphtpy.mm"
include "isphtpy.mm"
include "mpbid.mm"
include "simprd.mm"
include "oveq2.mm"
include "eqeq1d.mm"
include "anbi12d.mm"
include "rspccva.mm"
include "sylan.mm"

theorem phtpyi
  let wph: wff ph
  let cA: class A
  let cF: class F
  let cG: class G
  let cH: class H
  let cJ: class J
  let vs: setvar s
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vt: setvar t
  let vx: setvar x
  let vy: setvar y
  let cK: class K
  let vj: setvar j
  assume isphtpy.2: |- ( ph -> F e. ( II Cn J ) )
  assume isphtpy.3: |- ( ph -> G e. ( II Cn J ) )
  assume phtpyi.1: |- ( ph -> H e. ( F ( PHtpy ` J ) G ) )


  assert |- ( ( ph /\ A e. ( 0 [,] 1 ) ) -> ( ( 0 H A ) = ( F ` 0 ) /\ ( 1 H A ) = ( F ` 1 ) ) )

  proof
    wph
    cc0
    vs
    cv
    #
    cH
    co
    #
    cc0
    cF
    cfv
    #
    wceq
    #
    c1
    @0
    cH
    co
    #
    c1
    cF
    cfv
    #
    wceq
    #
    wa
    #
    vs
    cc0
    c1
    cicc
    co
    #
    wral
    #
    cA
    @8
    wcel
    cc0
    cA
    cH
    co
    #
    @2
    wceq
    #
    c1
    cA
    cH
    co
    #
    @5
    wceq
    #
    wa
    #
    wph
    cH
    cF
    cG
    cii
    cJ
    chtpy
    co
    co
    wcel
    #
    @9
    wph
    cH
    cF
    cG
    cJ
    cphtpy
    cfv
    co
    wcel
    @15
    @9
    wa
    phtpyi.1
    wph
    cF
    cG
    cH
    cJ
    vs
    isphtpy.2
    isphtpy.3
    isphtpy
    mpbid
    simprd
    @7
    @14
    vs
    cA
    @8
    @0
    cA
    wceq
    #
    @3
    @11
    @6
    @13
    @16
    @1
    @10
    @2
    @0
    cA
    cc0
    cH
    oveq2
    eqeq1d
    @16
    @4
    @12
    @5
    @0
    cA
    c1
    cH
    oveq2
    eqeq1d
    anbi12d
    rspccva
    sylan
end
