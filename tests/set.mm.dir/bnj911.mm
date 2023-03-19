include "cv.mm"
include "wfn.mm"
include "csuc.mm"
include "wcel.mm"
include "cfv.mm"
include "c-bnj14.mm"
include "ciun.mm"
include "wceq.mm"
include "wi.mm"
include "com.mm"
include "bnj1095.mm"
include "bnj1350.mm"

theorem bnj911
  let wph: wff ph
  let wps: wff ps
  let vy: setvar y
  let cA: class A
  let cR: class R
  let vf: setvar f
  let vi: setvar i
  let vn: setvar n
  let cX: class X
  assume bnj911.1: |- ( ph <-> ( f ` (/) ) = _pred ( X , A , R ) )
  assume bnj911.2: |- ( ps <-> A. i e. _om ( suc i e. n -> ( f ` suc i ) = U_ y e. ( f ` i ) _pred ( y , A , R ) ) )

  disjoint f i
  disjoint i n
  disjoint i ph
  assert |- ( ( f Fn n /\ ph /\ ps ) -> A. i ( f Fn n /\ ph /\ ps ) )

  proof
    vf
    cv
    #
    vn
    cv
    #
    wfn
    wph
    wps
    vi
    wps
    vi
    cv
    #
    csuc
    #
    @1
    wcel
    @3
    @0
    cfv
    vy
    @2
    @0
    cfv
    cA
    cR
    vy
    cv
    c-bnj14
    ciun
    wceq
    wi
    vi
    com
    bnj911.2
    bnj1095
    bnj1350
end
