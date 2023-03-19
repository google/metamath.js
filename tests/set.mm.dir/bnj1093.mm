include "cv.mm"
include "cfv.mm"
include "wss.mm"
include "wi.mm"
include "wex.mm"
include "wal.mm"
include "w3a.mm"
include "wcel.mm"
include "wfn.mm"
include "csuc.mm"
include "c-bnj14.mm"
include "ciun.mm"
include "wceq.mm"
include "com.mm"
include "bnj1095.mm"
include "bnj1096.mm"
include "bnj1350.mm"
include "wa.mm"
include "impexp.mm"
include "exbii.mm"
include "mpbi.mm"
include "19.37iv.mm"
include "alrimih.mm"
include "bnj721.mm"

theorem bnj1093
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wze: wff ze
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let vf: setvar f
  let vi: setvar i
  let vj: setvar j
  let vn: setvar n
  let bnjwph0: wff ph0
  assume bnj1093.1: |- E. j ( ( ( th /\ ta /\ ch ) /\ ph0 ) -> ( f ` i ) C_ B )
  assume bnj1093.2: |- ( ps <-> A. i e. _om ( suc i e. n -> ( f ` suc i ) = U_ y e. ( f ` i ) _pred ( y , A , R ) ) )
  assume bnj1093.3: |- ( ch <-> ( n e. D /\ f Fn n /\ ph /\ ps ) )

  disjoint ch j
  disjoint i ta
  disjoint i th
  disjoint j ta
  disjoint j th
  disjoint D i
  disjoint f i
  disjoint i n
  disjoint i ph
  assert |- ( ( th /\ ta /\ ch /\ ze ) -> A. i E. j ( ph0 -> ( f ` i ) C_ B ) )

  proof
    wth
    wta
    wch
    wze
    bnjwph0
    vi
    cv
    #
    vf
    cv
    #
    cfv
    #
    cB
    wss
    #
    wi
    #
    vj
    wex
    #
    vi
    wal
    wth
    wta
    wch
    w3a
    #
    @5
    vi
    wth
    wta
    wch
    vi
    wps
    wch
    vn
    cv
    #
    cD
    wcel
    @1
    @7
    wfn
    wph
    vi
    wps
    @0
    csuc
    #
    @7
    wcel
    @8
    @1
    cfv
    vy
    @2
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
    bnj1093.2
    bnj1095
    bnj1093.3
    bnj1096
    bnj1350
    @6
    @4
    vj
    @6
    bnjwph0
    wa
    @3
    wi
    #
    vj
    wex
    @6
    @4
    wi
    #
    vj
    wex
    bnj1093.1
    @9
    @10
    vj
    @6
    bnjwph0
    @3
    impexp
    exbii
    mpbi
    19.37iv
    alrimih
    bnj721
end
