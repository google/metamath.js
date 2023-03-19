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
include "ishtpyd.mm"
include "isphtpyd.mm"

theorem isphtpy2d
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
  assume isphtpy2d.1: |- ( ph -> H e. ( ( II tX II ) Cn J ) )
  assume isphtpy2d.2: |- ( ( ph /\ s e. ( 0 [,] 1 ) ) -> ( s H 0 ) = ( F ` s ) )
  assume isphtpy2d.3: |- ( ( ph /\ s e. ( 0 [,] 1 ) ) -> ( s H 1 ) = ( G ` s ) )
  assume isphtpy2d.4: |- ( ( ph /\ s e. ( 0 [,] 1 ) ) -> ( 0 H s ) = ( F ` 0 ) )
  assume isphtpy2d.5: |- ( ( ph /\ s e. ( 0 [,] 1 ) ) -> ( 1 H s ) = ( F ` 1 ) )

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
    cF
    cG
    cH
    cJ
    vs
    isphtpy.2
    isphtpy.3
    wph
    cF
    cG
    cH
    cii
    cJ
    cc0
    c1
    cicc
    co
    #
    vs
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
    isphtpy2d.1
    isphtpy2d.2
    isphtpy2d.3
    ishtpyd
    isphtpy2d.4
    isphtpy2d.5
    isphtpyd
end
