include "cv.mm"
include "cle.mm"
include "cofr.mm"
include "wbr.mm"
include "citg1.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "cdm.mm"
include "wrex.mm"
include "cab.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cr.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "citg2.mm"
include "xrltso.mm"
include "supex.mm"
include "reex.mm"
include "ovex.mm"
include "breq2.mm"
include "anbi1d.mm"
include "rexbidv.mm"
include "abbidv.mm"
include "syl6eqr.mm"
include "supeq1d.mm"
include "df-itg2.mm"
include "fvmptmap.mm"

theorem itg2val
  let vx: setvar x
  let vg: setvar g
  let cF: class F
  let cL: class L
  let cA: class A
  let vf: setvar f
  let cG: class G
  assume itg2val.1: |- L = { x | E. g e. dom S.1 ( g oR <_ F /\ x = ( S.1 ` g ) ) }

  disjoint g x
  disjoint F g
  disjoint F x
  disjoint A g
  disjoint A x
  disjoint f g
  disjoint f x
  disjoint F f
  disjoint G g
  disjoint G x
  disjoint L f
  assert |- ( F : RR --> ( 0 [,] +oo ) -> ( S.2 ` F ) = sup ( L , RR* , < ) )

  proof
    vf
    cF
    vg
    cv
    #
    vf
    cv
    #
    cle
    cofr
    #
    wbr
    #
    vx
    cv
    @0
    citg1
    cfv
    wceq
    #
    wa
    #
    vg
    citg1
    cdm
    #
    wrex
    #
    vx
    cab
    #
    cxr
    clt
    csup
    cL
    cxr
    clt
    csup
    cr
    cc0
    cpnf
    cicc
    co
    citg2
    cxr
    cL
    clt
    xrltso
    supex
    reex
    cc0
    cpnf
    cicc
    ovex
    @1
    cF
    wceq
    #
    cxr
    @8
    cL
    clt
    @9
    @8
    @0
    cF
    @2
    wbr
    #
    @4
    wa
    #
    vg
    @6
    wrex
    #
    vx
    cab
    cL
    @9
    @7
    @12
    vx
    @9
    @5
    @11
    vg
    @6
    @9
    @3
    @10
    @4
    @1
    cF
    @0
    @2
    breq2
    anbi1d
    rexbidv
    abbidv
    itg2val.1
    syl6eqr
    supeq1d
    vx
    vf
    vg
    df-itg2
    fvmptmap
end
