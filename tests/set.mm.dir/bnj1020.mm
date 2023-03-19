include "wex.mm"
include "w-bnj17.mm"
include "cv.mm"
include "c-bnj14.mm"
include "csuc.mm"
include "cfv.mm"
include "c-bnj18.mm"
include "wss.mm"
include "bnj1019.mm"
include "bnj998.mm"
include "bnj1001.mm"
include "bnj1006.mm"
include "exlimiv.mm"
include "sylbir.mm"
include "bnj1018.mm"
include "sstrd.mm"

theorem bnj1020
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
  assume bnj1020.1: |- ( ph <-> ( f ` (/) ) = _pred ( X , A , R ) )
  assume bnj1020.2: |- ( ps <-> A. i e. _om ( suc i e. n -> ( f ` suc i ) = U_ y e. ( f ` i ) _pred ( y , A , R ) ) )
  assume bnj1020.3: |- ( ch <-> ( n e. D /\ f Fn n /\ ph /\ ps ) )
  assume bnj1020.4: |- ( th <-> ( R _FrSe A /\ X e. A /\ y e. _trCl ( X , A , R ) /\ z e. _pred ( y , A , R ) ) )
  assume bnj1020.5: |- ( ta <-> ( m e. _om /\ n = suc m /\ p = suc n ) )
  assume bnj1020.6: |- ( et <-> ( i e. n /\ y e. ( f ` i ) ) )
  assume bnj1020.7: |- ( ph' <-> [. p / n ]. ph )
  assume bnj1020.8: |- ( ps' <-> [. p / n ]. ps )
  assume bnj1020.9: |- ( ch' <-> [. p / n ]. ch )
  assume bnj1020.10: |- ( ph" <-> [. G / f ]. ph' )
  assume bnj1020.11: |- ( ps" <-> [. G / f ]. ps' )
  assume bnj1020.12: |- ( ch" <-> [. G / f ]. ch' )
  assume bnj1020.13: |- D = ( _om \ { (/) } )
  assume bnj1020.14: |- B = { f | E. n e. D ( f Fn n /\ ph /\ ps ) }
  assume bnj1020.15: |- C = U_ y e. ( f ` m ) _pred ( y , A , R )
  assume bnj1020.16: |- G = ( f u. { <. n , C >. } )
  assume bnj1020.26: |- ( ch" <-> ( p e. D /\ G Fn p /\ ph" /\ ps" ) )

  disjoint A f
  disjoint A i
  disjoint A m
  disjoint A n
  disjoint A y
  disjoint f i
  disjoint f m
  disjoint f n
  disjoint f y
  disjoint i m
  disjoint i n
  disjoint i y
  disjoint m n
  disjoint m y
  disjoint n y
  disjoint A p
  disjoint f p
  disjoint i p
  disjoint n p
  disjoint p y
  disjoint D f
  disjoint D i
  disjoint D n
  disjoint G i
  disjoint G p
  disjoint R f
  disjoint R i
  disjoint R m
  disjoint R n
  disjoint R y
  disjoint R p
  disjoint X f
  disjoint X i
  disjoint X n
  disjoint X y
  disjoint ch p
  disjoint et p
  disjoint i ph
  disjoint p th
  assert |- ( ( th /\ ch /\ et /\ E. p ta ) -> _pred ( y , A , R ) C_ _trCl ( X , A , R ) )

  proof
    wth
    wch
    wet
    wta
    vp
    wex
    w-bnj17
    #
    cA
    cR
    vy
    cv
    c-bnj14
    #
    vi
    cv
    csuc
    cG
    cfv
    #
    cA
    cR
    cX
    c-bnj18
    @0
    wth
    wch
    wta
    wet
    w-bnj17
    #
    vp
    wex
    @1
    @2
    wss
    #
    wch
    wth
    wta
    wet
    vp
    bnj1019
    @3
    @4
    vp
    wph
    wps
    wch
    wth
    wta
    wet
    vy
    vz
    cA
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
    bnj1020.1
    bnj1020.2
    bnj1020.3
    bnj1020.4
    bnj1020.5
    bnj1020.6
    bnj1020.7
    bnj1020.8
    bnj1020.9
    bnj1020.10
    bnj1020.11
    bnj1020.12
    bnj1020.13
    bnj1020.15
    bnj1020.16
    wph
    wps
    wch
    wth
    wta
    wet
    vy
    cD
    vf
    vi
    vm
    vn
    vp
    bnjwchn
    bnj1020.3
    bnj1020.5
    bnj1020.6
    bnj1020.13
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
    bnj1020.1
    bnj1020.2
    bnj1020.3
    bnj1020.4
    bnj1020.5
    bnj1020.7
    bnj1020.8
    bnj1020.9
    bnj1020.10
    bnj1020.11
    bnj1020.12
    bnj1020.13
    bnj1020.14
    bnj1020.15
    bnj1020.16
    bnj998
    #
    bnj1001
    #
    bnj1006
    exlimiv
    sylbir
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
    bnj1020.1
    bnj1020.2
    bnj1020.3
    bnj1020.4
    bnj1020.5
    bnj1020.7
    bnj1020.8
    bnj1020.9
    bnj1020.10
    bnj1020.11
    bnj1020.12
    bnj1020.13
    bnj1020.14
    bnj1020.15
    bnj1020.16
    bnj1020.26
    @5
    @6
    bnj1018
    sstrd
end
