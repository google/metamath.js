include "citg1.mm"
include "cdm.mm"
include "wcel.mm"
include "cle.mm"
include "cofr.mm"
include "wbr.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wrex.mm"
include "eqid.mm"
include "breq1.mm"
include "fveq2.mm"
include "eqeq2d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "mpanr2.mm"
include "itg2l.mm"
include "sylibr.mm"

theorem itg2lr
  let vx: setvar x
  let vg: setvar g
  let cF: class F
  let cG: class G
  let cL: class L
  let cA: class A
  let vf: setvar f
  assume itg2val.1: |- L = { x | E. g e. dom S.1 ( g oR <_ F /\ x = ( S.1 ` g ) ) }

  disjoint g x
  disjoint F g
  disjoint F x
  disjoint G g
  disjoint G x
  disjoint A g
  disjoint A x
  disjoint f g
  disjoint f x
  disjoint F f
  disjoint L f
  assert |- ( ( G e. dom S.1 /\ G oR <_ F ) -> ( S.1 ` G ) e. L )

  proof
    cG
    citg1
    cdm
    #
    wcel
    #
    cG
    cF
    cle
    cofr
    #
    wbr
    #
    wa
    vg
    cv
    #
    cF
    @2
    wbr
    #
    cG
    citg1
    cfv
    #
    @4
    citg1
    cfv
    #
    wceq
    #
    wa
    #
    vg
    @0
    wrex
    #
    @6
    cL
    wcel
    @1
    @3
    @6
    @6
    wceq
    #
    @10
    @6
    eqid
    @9
    @3
    @11
    wa
    vg
    cG
    @0
    @4
    cG
    wceq
    #
    @5
    @3
    @8
    @11
    @4
    cG
    cF
    @2
    breq1
    @12
    @7
    @6
    @6
    @4
    cG
    citg1
    fveq2
    eqeq2d
    anbi12d
    rspcev
    mpanr2
    vx
    @6
    vg
    cF
    cL
    itg2val.1
    itg2l
    sylibr
end
