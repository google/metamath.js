include "cv.mm"
include "c-bnj14.mm"
include "c-bnj18.mm"
include "wss.mm"
include "wi.mm"
include "wex.mm"
include "w-bnj17.mm"
include "bnj1021.mm"
include "wal.mm"
include "vex.mm"
include "bnj919.mm"
include "bnj918.mm"
include "bnj976.mm"
include "bnj1020.mm"
include "ax-gen.mm"
include "wa.mm"
include "19.29r.mm"
include "pm3.33.mm"
include "bnj593.mm"
include "mpan2.mm"
include "2eximi.mm"
include "bnj101.mm"
include "19.9v.mm"
include "mpbi.mm"
include "w-bnj15.mm"
include "wcel.mm"
include "bnj1254.mm"
include "sseldd.mm"
include "bnj978.mm"

theorem bnj907
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let vf: setvar f
  let vi: setvar i
  let vm: setvar m
  let vn: setvar n
  let cG: class G
  let cX: class X
  let vp: setvar p
  let bnjwphm: wff ph'
  let bnjwpsm: wff ps'
  let bnjwchm: wff ch'
  let bnjwphn: wff ph"
  let bnjwpsn: wff ps"
  let bnjwchn: wff ch"
  assume bnj907.1: |- ( ph <-> ( f ` (/) ) = _pred ( X , A , R ) )
  assume bnj907.2: |- ( ps <-> A. i e. _om ( suc i e. n -> ( f ` suc i ) = U_ y e. ( f ` i ) _pred ( y , A , R ) ) )
  assume bnj907.3: |- ( ch <-> ( n e. D /\ f Fn n /\ ph /\ ps ) )
  assume bnj907.4: |- ( th <-> ( R _FrSe A /\ X e. A /\ y e. _trCl ( X , A , R ) /\ z e. _pred ( y , A , R ) ) )
  assume bnj907.5: |- ( ta <-> ( m e. _om /\ n = suc m /\ p = suc n ) )
  assume bnj907.6: |- ( et <-> ( i e. n /\ y e. ( f ` i ) ) )
  assume bnj907.7: |- ( ph' <-> [. p / n ]. ph )
  assume bnj907.8: |- ( ps' <-> [. p / n ]. ps )
  assume bnj907.9: |- ( ch' <-> [. p / n ]. ch )
  assume bnj907.10: |- ( ph" <-> [. G / f ]. ph' )
  assume bnj907.11: |- ( ps" <-> [. G / f ]. ps' )
  assume bnj907.12: |- ( ch" <-> [. G / f ]. ch' )
  assume bnj907.13: |- D = ( _om \ { (/) } )
  assume bnj907.14: |- B = { f | E. n e. D ( f Fn n /\ ph /\ ps ) }
  assume bnj907.15: |- C = U_ y e. ( f ` m ) _pred ( y , A , R )
  assume bnj907.16: |- G = ( f u. { <. n , C >. } )

  disjoint A f
  disjoint A i
  disjoint A m
  disjoint A n
  disjoint A p
  disjoint A y
  disjoint f i
  disjoint f m
  disjoint f n
  disjoint f p
  disjoint f y
  disjoint i m
  disjoint i n
  disjoint i p
  disjoint i y
  disjoint m n
  disjoint m p
  disjoint m y
  disjoint n p
  disjoint n y
  disjoint p y
  disjoint A z
  disjoint y z
  disjoint D f
  disjoint D i
  disjoint D n
  disjoint G i
  disjoint G p
  disjoint R f
  disjoint R i
  disjoint R m
  disjoint R n
  disjoint R p
  disjoint R y
  disjoint R z
  disjoint X f
  disjoint X i
  disjoint X m
  disjoint X n
  disjoint X y
  disjoint X z
  disjoint ch m
  disjoint ch p
  disjoint et m
  disjoint et p
  disjoint f th
  disjoint i th
  disjoint m th
  disjoint n th
  disjoint p th
  disjoint i ph
  assert |- ( ( R _FrSe A /\ X e. A ) -> _TrFo ( _trCl ( X , A , R ) , A , R ) )

  proof
    wth
    vy
    vz
    cA
    cR
    cX
    bnj907.4
    wth
    cA
    cR
    vy
    cv
    #
    c-bnj14
    #
    cA
    cR
    cX
    c-bnj18
    #
    vz
    cv
    #
    wth
    @1
    @2
    wss
    #
    wi
    #
    vm
    wex
    #
    @5
    @6
    vi
    wex
    #
    @6
    @7
    vn
    wex
    #
    @7
    @8
    vf
    wex
    @8
    wth
    wth
    wch
    wet
    wta
    vp
    wex
    w-bnj17
    #
    wi
    #
    vm
    wex
    #
    vi
    wex
    vn
    wex
    @8
    vf
    wph
    wps
    wch
    wth
    wta
    wet
    vy
    vz
    cA
    cB
    cD
    cR
    vf
    vi
    vm
    vn
    cX
    vp
    bnj907.1
    bnj907.2
    bnj907.3
    bnj907.4
    bnj907.5
    bnj907.6
    bnj907.13
    bnj907.14
    bnj1021
    @11
    @6
    vn
    vi
    @11
    @9
    @4
    wi
    #
    vm
    wal
    #
    @6
    @12
    vm
    wph
    wps
    wch
    wth
    wta
    wet
    vy
    vz
    cA
    cB
    cC
    cD
    cR
    vf
    vi
    vm
    vn
    cG
    cX
    vp
    bnjwphm
    bnjwpsm
    bnjwchm
    bnjwphn
    bnjwpsn
    bnjwchn
    bnj907.1
    bnj907.2
    bnj907.3
    bnj907.4
    bnj907.5
    bnj907.6
    bnj907.7
    bnj907.8
    bnj907.9
    bnj907.10
    bnj907.11
    bnj907.12
    bnj907.13
    bnj907.14
    bnj907.15
    bnj907.16
    bnjwphm
    bnjwpsm
    bnjwchm
    cD
    vf
    cG
    vp
    cv
    #
    bnjwphn
    bnjwpsn
    bnjwchn
    wph
    wps
    wch
    cD
    @14
    vn
    vf
    cv
    bnjwphm
    bnjwpsm
    bnjwchm
    bnj907.3
    bnj907.7
    bnj907.8
    bnj907.9
    vp
    vex
    bnj919
    bnj907.10
    bnj907.11
    bnj907.12
    cC
    vf
    vn
    cG
    bnj907.16
    bnj918
    bnj976
    bnj1020
    ax-gen
    @11
    @13
    wa
    @10
    @12
    wa
    @5
    vm
    @10
    @12
    vm
    19.29r
    wth
    @9
    @4
    pm3.33
    bnj593
    mpan2
    2eximi
    bnj101
    @8
    vf
    19.9v
    mpbi
    @7
    vn
    19.9v
    mpbi
    @6
    vi
    19.9v
    mpbi
    @5
    vm
    19.9v
    mpbi
    wth
    cA
    cR
    w-bnj15
    cX
    cA
    wcel
    @0
    @2
    wcel
    @3
    @1
    wcel
    bnj907.4
    bnj1254
    sseldd
    bnj978
end
