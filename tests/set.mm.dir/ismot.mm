include "wcel.mm"
include "cismt.mm"
include "co.mm"
include "wf1o.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "wb.mm"
include "isismt.mm"
include "anidms.mm"

theorem ismot
  let cP: class P
  let cF: class F
  let cG: class G
  let c.mi: class .-
  let cV: class V
  let va: setvar a
  let vb: setvar b
  assume ismot.p: |- P = ( Base ` G )
  assume ismot.m: |- .- = ( dist ` G )

  disjoint F a
  disjoint F b
  disjoint a b
  disjoint G a
  disjoint G b
  disjoint P a
  disjoint P b
  assert |- ( G e. V -> ( F e. ( G Ismt G ) <-> ( F : P -1-1-onto-> P /\ A. a e. P A. b e. P ( ( F ` a ) .- ( F ` b ) ) = ( a .- b ) ) ) )

  proof
    cG
    cV
    wcel
    cF
    cG
    cG
    cismt
    co
    wcel
    cP
    cP
    cF
    wf1o
    va
    cv
    #
    cF
    cfv
    vb
    cv
    #
    cF
    cfv
    c.mi
    co
    @0
    @1
    c.mi
    co
    wceq
    vb
    cP
    wral
    va
    cP
    wral
    wa
    wb
    cP
    c.mi
    cP
    cF
    cG
    cG
    c.mi
    cV
    cV
    va
    vb
    ismot.p
    ismot.p
    ismot.m
    ismot.m
    isismt
    anidms
end
