include "cv.mm"
include "wfn.mm"
include "w3a.mm"
include "wcel.mm"
include "wsbc.mm"
include "cfv.mm"
include "wceq.mm"
include "wi.mm"
include "cep.mm"
include "wbr.mm"
include "wral.mm"
include "biid.mm"
include "bnj580.mm"

theorem bnj579
  let wph: wff ph
  let wps: wff ps
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cD: class D
  let cR: class R
  let vf: setvar f
  let vi: setvar i
  let vn: setvar n
  let vk: setvar k
  let vg: setvar g
  let vj: setvar j
  assume bnj579.1: |- ( ph <-> ( f ` (/) ) = _pred ( x , A , R ) )
  assume bnj579.2: |- ( ps <-> A. i e. _om ( suc i e. n -> ( f ` suc i ) = U_ y e. ( f ` i ) _pred ( y , A , R ) ) )
  assume bnj579.3: |- D = ( _om \ { (/) } )

  disjoint A f
  disjoint A i
  disjoint f i
  disjoint D f
  disjoint R f
  disjoint R i
  disjoint f n
  disjoint i n
  disjoint f x
  disjoint f y
  disjoint i y
  disjoint A k
  disjoint f k
  disjoint i k
  disjoint D g
  disjoint D j
  disjoint D k
  disjoint f g
  disjoint f j
  disjoint g j
  disjoint g k
  disjoint j k
  disjoint R k
  disjoint g i
  disjoint g n
  disjoint k n
  disjoint g y
  disjoint k y
  disjoint g ph
  disjoint j ph
  disjoint k ph
  disjoint g ps
  disjoint j ps
  disjoint k ps
  disjoint j n
  assert |- ( n e. D -> E* f ( f Fn n /\ ph /\ ps ) )

  proof
    wph
    wps
    vf
    cv
    #
    vn
    cv
    #
    wfn
    wph
    wps
    w3a
    #
    @1
    cD
    wcel
    @2
    @2
    vf
    vg
    cv
    #
    wsbc
    #
    w3a
    vj
    cv
    #
    @0
    cfv
    @5
    @3
    cfv
    wceq
    wi
    #
    vk
    cv
    #
    @5
    cep
    wbr
    @6
    vj
    @7
    wsbc
    wi
    vk
    @1
    wral
    #
    vx
    vy
    cA
    cD
    cR
    vf
    vg
    vi
    vj
    vk
    vn
    wph
    vf
    @3
    wsbc
    #
    wps
    vf
    @3
    wsbc
    #
    @4
    bnj579.1
    bnj579.2
    @2
    biid
    @9
    biid
    @10
    biid
    @4
    biid
    bnj579.3
    @6
    biid
    @8
    biid
    bnj580
end
