include "cphtpy.mm"
include "cfv.mm"
include "co.mm"
include "wcel.mm"
include "cii.mm"
include "chtpy.mm"
include "cc0.mm"
include "cv.mm"
include "wceq.mm"
include "c1.mm"
include "wa.mm"
include "cicc.mm"
include "wral.mm"
include "jca.mm"
include "ralrimiva.mm"
include "isphtpy.mm"
include "mpbir2and.mm"

theorem isphtpyd
  let wph: wff ph
  let cF: class F
  let cG: class G
  let cH: class H
  let cJ: class J
  let vs: setvar s
  let cA: class A
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
  assume isphtpyd.1: |- ( ph -> H e. ( F ( II Htpy J ) G ) )
  assume isphtpyd.2: |- ( ( ph /\ s e. ( 0 [,] 1 ) ) -> ( 0 H s ) = ( F ` 0 ) )
  assume isphtpyd.3: |- ( ( ph /\ s e. ( 0 [,] 1 ) ) -> ( 1 H s ) = ( F ` 1 ) )

  disjoint F s
  disjoint G s
  disjoint H s
  disjoint J s
  disjoint ph s
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
  disjoint F t
  disjoint G f
  disjoint G g
  disjoint G h
  disjoint G t
  disjoint h x
  disjoint h y
  disjoint H h
  disjoint s x
  disjoint s y
  disjoint x y
  disjoint H x
  disjoint H y
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
  disjoint t x
  disjoint t y
  disjoint J t
  disjoint J x
  disjoint J y
  disjoint f ph
  disjoint g ph
  disjoint h ph
  disjoint ph t
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> H e. ( F ( PHtpy ` J ) G ) )

  proof
    wph
    cH
    cF
    cG
    cJ
    cphtpy
    cfv
    co
    wcel
    cH
    cF
    cG
    cii
    cJ
    chtpy
    co
    co
    wcel
    cc0
    vs
    cv
    #
    cH
    co
    cc0
    cF
    cfv
    wceq
    #
    c1
    @0
    cH
    co
    c1
    cF
    cfv
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
    isphtpyd.1
    wph
    @3
    vs
    @4
    wph
    @0
    @4
    wcel
    wa
    @1
    @2
    isphtpyd.2
    isphtpyd.3
    jca
    ralrimiva
    wph
    cF
    cG
    cH
    cJ
    vs
    isphtpy.2
    isphtpy.3
    isphtpy
    mpbir2and
end
