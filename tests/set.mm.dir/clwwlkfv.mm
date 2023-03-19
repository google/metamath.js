include "cv.mm"
include "cc0.mm"
include "cop.mm"
include "csubstr.mm"
include "co.mm"
include "oveq1.mm"
include "ovex.mm"
include "fvmpt.mm"

theorem clwwlkfv
  let vw: setvar w
  let vt: setvar t
  let cD: class D
  let cF: class F
  let cG: class G
  let cN: class N
  let cW: class W
  let vi: setvar i
  let cP: class P
  assume clwwlkbij.d: |- D = { w e. ( N WWalksN G ) | ( lastS ` w ) = ( w ` 0 ) }
  assume clwwlkbij.f: |- F = ( t e. D |-> ( t substr <. 0 , N >. ) )

  disjoint G w
  disjoint N w
  disjoint D t
  disjoint G t
  disjoint t w
  disjoint N t
  disjoint W t
  disjoint G i
  disjoint N i
  disjoint P i
  disjoint P w
  disjoint i t
  assert |- ( W e. D -> ( F ` W ) = ( W substr <. 0 , N >. ) )

  proof
    vt
    cW
    vt
    cv
    #
    cc0
    cN
    cop
    #
    csubstr
    co
    cW
    @1
    csubstr
    co
    cD
    cF
    @0
    cW
    @1
    csubstr
    oveq1
    clwwlkbij.f
    cW
    @1
    csubstr
    ovex
    fvmpt
end
