include "cv.mm"
include "c-bnj18.mm"
include "wcel.mm"
include "wfn.mm"
include "w3a.mm"
include "cfv.mm"
include "w-bnj17.mm"
include "wex.mm"
include "biid.mm"
include "bnj916.mm"
include "wa.mm"
include "bnj252.mm"
include "bitri.mm"
include "3anbi1i.mm"
include "bnj253.mm"
include "bitr4i.mm"
include "3exbii.mm"
include "sylibr.mm"

theorem bnj917
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let vf: setvar f
  let vi: setvar i
  let vn: setvar n
  let cX: class X
  assume bnj917.1: |- ( ph <-> ( f ` (/) ) = _pred ( X , A , R ) )
  assume bnj917.2: |- ( ps <-> A. i e. _om ( suc i e. n -> ( f ` suc i ) = U_ y e. ( f ` i ) _pred ( y , A , R ) ) )
  assume bnj917.3: |- D = ( _om \ { (/) } )
  assume bnj917.4: |- B = { f | E. n e. D ( f Fn n /\ ph /\ ps ) }
  assume bnj917.5: |- ( ch <-> ( n e. D /\ f Fn n /\ ph /\ ps ) )

  disjoint A f
  disjoint A i
  disjoint A n
  disjoint A y
  disjoint f i
  disjoint f n
  disjoint f y
  disjoint i n
  disjoint i y
  disjoint n y
  disjoint D i
  disjoint R f
  disjoint R i
  disjoint R n
  disjoint R y
  disjoint X f
  disjoint X i
  disjoint X n
  disjoint X y
  disjoint i ph
  assert |- ( y e. _trCl ( X , A , R ) -> E. f E. n E. i ( ch /\ i e. n /\ y e. ( f ` i ) ) )

  proof
    vy
    cv
    #
    cA
    cR
    cX
    c-bnj18
    wcel
    vn
    cv
    #
    cD
    wcel
    #
    vf
    cv
    #
    @1
    wfn
    #
    wph
    wps
    w3a
    #
    vi
    cv
    #
    @1
    wcel
    #
    @0
    @6
    @3
    cfv
    wcel
    #
    w-bnj17
    #
    vi
    wex
    vn
    wex
    vf
    wex
    wch
    @7
    @8
    w3a
    #
    vi
    wex
    vn
    wex
    vf
    wex
    wph
    wps
    @5
    vy
    cA
    cB
    cD
    cR
    vf
    vi
    vn
    cX
    bnj917.1
    bnj917.2
    bnj917.3
    bnj917.4
    @5
    biid
    bnj916
    @10
    @9
    vf
    vn
    vi
    @10
    @2
    @5
    wa
    #
    @7
    @8
    w3a
    @9
    wch
    @11
    @7
    @8
    wch
    @2
    @4
    wph
    wps
    w-bnj17
    @11
    bnj917.5
    @2
    @4
    wph
    wps
    bnj252
    bitri
    3anbi1i
    @2
    @5
    @7
    @8
    bnj253
    bitr4i
    3exbii
    sylibr
end
