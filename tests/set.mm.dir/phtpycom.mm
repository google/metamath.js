include "cii.mm"
include "cc0.mm"
include "c1.mm"
include "cicc.mm"
include "co.mm"
include "ctopon.mm"
include "cfv.mm"
include "wcel.mm"
include "iitopon.mm"
include "a1i.mm"
include "cphtpy.mm"
include "chtpy.mm"
include "phtpyhtpy.mm"
include "sseldd.mm"
include "htpycom.mm"
include "cv.mm"
include "wa.mm"
include "cmin.mm"
include "wceq.mm"
include "0elunit.mm"
include "simpr.mm"
include "oveq1.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "ovex.mm"
include "ovmpt2.mm"
include "sylancr.mm"
include "iirev.mm"
include "phtpyi.mm"
include "sylan2.mm"
include "simpld.mm"
include "phtpy01.mm"
include "adantr.mm"
include "3eqtrd.mm"
include "1elunit.mm"
include "simprd.mm"
include "isphtpyd.mm"

theorem phtpycom
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cF: class F
  let cG: class G
  let cH: class H
  let cJ: class J
  let cK: class K
  let cA: class A
  let vs: setvar s
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vt: setvar t
  let vj: setvar j
  assume isphtpy.2: |- ( ph -> F e. ( II Cn J ) )
  assume isphtpy.3: |- ( ph -> G e. ( II Cn J ) )
  assume phtpycom.6: |- K = ( x e. ( 0 [,] 1 ) , y e. ( 0 [,] 1 ) |-> ( x H ( 1 - y ) ) )
  assume phtpycom.7: |- ( ph -> H e. ( F ( PHtpy ` J ) G ) )

  disjoint x y
  disjoint H x
  disjoint H y
  disjoint J x
  disjoint J y
  disjoint ph x
  disjoint ph y
  disjoint A s
  disjoint f g
  disjoint f h
  disjoint f s
  disjoint f t
  disjoint F f
  disjoint g h
  disjoint g s
  disjoint g t
  disjoint F g
  disjoint h s
  disjoint h t
  disjoint F h
  disjoint s t
  disjoint F s
  disjoint F t
  disjoint G f
  disjoint G g
  disjoint G h
  disjoint G s
  disjoint G t
  disjoint h x
  disjoint h y
  disjoint H h
  disjoint s x
  disjoint s y
  disjoint H s
  disjoint K t
  disjoint f j
  disjoint f x
  disjoint f y
  disjoint J f
  disjoint g j
  disjoint g x
  disjoint g y
  disjoint J g
  disjoint h j
  disjoint J h
  disjoint j s
  disjoint j t
  disjoint j x
  disjoint j y
  disjoint J j
  disjoint J s
  disjoint t x
  disjoint t y
  disjoint J t
  disjoint f ph
  disjoint g ph
  disjoint h ph
  disjoint ph s
  disjoint ph t
  assert |- ( ph -> K e. ( G ( PHtpy ` J ) F ) )

  proof
    wph
    cG
    cF
    cK
    cJ
    vt
    isphtpy.3
    isphtpy.2
    wph
    vx
    vy
    cF
    cG
    cH
    cii
    cJ
    cK
    cc0
    c1
    cicc
    co
    #
    cii
    @0
    ctopon
    cfv
    wcel
    wph
    iitopon
    a1i
    isphtpy.2
    isphtpy.3
    phtpycom.6
    wph
    cF
    cG
    cJ
    cphtpy
    cfv
    co
    cF
    cG
    cii
    cJ
    chtpy
    co
    co
    cH
    wph
    cF
    cG
    cJ
    isphtpy.2
    isphtpy.3
    phtpyhtpy
    phtpycom.7
    sseldd
    htpycom
    wph
    vt
    cv
    #
    @0
    wcel
    #
    wa
    #
    cc0
    @1
    cK
    co
    #
    cc0
    c1
    @1
    cmin
    co
    #
    cH
    co
    #
    cc0
    cF
    cfv
    #
    cc0
    cG
    cfv
    #
    @3
    cc0
    @0
    wcel
    @2
    @4
    @6
    wceq
    0elunit
    wph
    @2
    simpr
    #
    vx
    vy
    cc0
    @1
    @0
    @0
    vx
    cv
    #
    c1
    vy
    cv
    #
    cmin
    co
    #
    cH
    co
    #
    @6
    cK
    cc0
    @12
    cH
    co
    @10
    cc0
    @12
    cH
    oveq1
    @11
    @1
    wceq
    #
    @12
    @5
    cc0
    cH
    @11
    @1
    c1
    cmin
    oveq2
    #
    oveq2d
    phtpycom.6
    cc0
    @5
    cH
    ovex
    ovmpt2
    sylancr
    @3
    @6
    @7
    wceq
    #
    c1
    @5
    cH
    co
    #
    c1
    cF
    cfv
    #
    wceq
    #
    @2
    wph
    @5
    @0
    wcel
    @16
    @19
    wa
    @1
    iirev
    wph
    @5
    cF
    cG
    cH
    cJ
    isphtpy.2
    isphtpy.3
    phtpycom.7
    phtpyi
    sylan2
    #
    simpld
    @3
    @7
    @8
    wceq
    #
    @18
    c1
    cG
    cfv
    #
    wceq
    #
    wph
    @21
    @23
    wa
    @2
    wph
    cF
    cG
    cH
    cJ
    isphtpy.2
    isphtpy.3
    phtpycom.7
    phtpy01
    adantr
    #
    simpld
    3eqtrd
    @3
    c1
    @1
    cK
    co
    #
    @17
    @18
    @22
    @3
    c1
    @0
    wcel
    @2
    @25
    @17
    wceq
    1elunit
    @9
    vx
    vy
    c1
    @1
    @0
    @0
    @13
    @17
    cK
    c1
    @12
    cH
    co
    @10
    c1
    @12
    cH
    oveq1
    @14
    @12
    @5
    c1
    cH
    @15
    oveq2d
    phtpycom.6
    c1
    @5
    cH
    ovex
    ovmpt2
    sylancr
    @3
    @16
    @19
    @20
    simprd
    @3
    @21
    @23
    @24
    simprd
    3eqtrd
    isphtpyd
end
