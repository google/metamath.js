include "w-bnj15.mm"
include "cv.mm"
include "wcel.mm"
include "w-bnj17.mm"
include "w3a.mm"
include "wfn.mm"
include "wa.mm"
include "wex.mm"
include "bnj248.mm"
include "weu.mm"
include "wi.mm"
include "vex.mm"
include "bnj207.mm"
include "biimpi.mm"
include "euex.mm"
include "syl6.mm"
include "impcom.mm"
include "bnj1198.mm"
include "bnj832.mm"
include "bnj645.mm"
include "19.41v.mm"
include "sylanbrc.mm"
include "bnj642.mm"
include "bnj170.mm"
include "bnj523.mm"
include "bnj539.mm"
include "bnj544.mm"
include "bnj561.mm"
include "bnj528.mm"
include "bnj609.mm"
include "bnj545.mm"
include "bnj562.mm"
include "bnj611.mm"
include "bnj571.mm"
include "3jca.mm"
include "bnj593.mm"

theorem bnj908
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let wze: wff ze
  let wsi: wff si
  let wrh: wff rh
  let vx: setvar x
  let vy: setvar y
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
  let cK: class K
  let cL: class L
  let vp: setvar p
  let bnjwphm: wff ph'
  let bnjwpsm: wff ps'
  let bnjwchm: wff ch'
  let bnjwphn: wff ph"
  let bnjwpsn: wff ps"
  let bnjwchn: wff ch"
  assume bnj908.1: |- ( ph <-> ( f ` (/) ) = _pred ( x , A , R ) )
  assume bnj908.2: |- ( ps <-> A. i e. _om ( suc i e. n -> ( f ` suc i ) = U_ y e. ( f ` i ) _pred ( y , A , R ) ) )
  assume bnj908.3: |- D = ( _om \ { (/) } )
  assume bnj908.4: |- ( ch <-> ( ( R _FrSe A /\ x e. A ) -> E! f ( f Fn n /\ ph /\ ps ) ) )
  assume bnj908.5: |- ( th <-> A. m e. D ( m _E n -> [. m / n ]. ch ) )
  assume bnj908.10: |- ( ph' <-> [. m / n ]. ph )
  assume bnj908.11: |- ( ps' <-> [. m / n ]. ps )
  assume bnj908.12: |- ( ch' <-> [. m / n ]. ch )
  assume bnj908.13: |- ( ph" <-> [. G / f ]. ph )
  assume bnj908.14: |- ( ps" <-> [. G / f ]. ps )
  assume bnj908.15: |- ( ch" <-> [. G / f ]. ch )
  assume bnj908.16: |- G = ( f u. { <. m , U_ y e. ( f ` p ) _pred ( y , A , R ) >. } )
  assume bnj908.17: |- ( ta <-> ( f Fn m /\ ph' /\ ps' ) )
  assume bnj908.18: |- ( si <-> ( m e. D /\ n = suc m /\ p e. m ) )
  assume bnj908.19: |- ( et <-> ( m e. D /\ n = suc m /\ p e. _om /\ m = suc p ) )
  assume bnj908.20: |- ( ze <-> ( i e. _om /\ suc i e. n /\ m = suc i ) )
  assume bnj908.21: |- ( rh <-> ( i e. _om /\ suc i e. n /\ m =/= suc i ) )
  assume bnj908.22: |- B = U_ y e. ( f ` i ) _pred ( y , A , R )
  assume bnj908.23: |- C = U_ y e. ( f ` p ) _pred ( y , A , R )
  assume bnj908.24: |- K = U_ y e. ( G ` i ) _pred ( y , A , R )
  assume bnj908.25: |- L = U_ y e. ( G ` p ) _pred ( y , A , R )
  assume bnj908.26: |- G = ( f u. { <. m , C >. } )

  disjoint A f
  disjoint A i
  disjoint A m
  disjoint A n
  disjoint A p
  disjoint f i
  disjoint f m
  disjoint f n
  disjoint f p
  disjoint i m
  disjoint i n
  disjoint i p
  disjoint m n
  disjoint m p
  disjoint n p
  disjoint A y
  disjoint f y
  disjoint i y
  disjoint n y
  disjoint p y
  disjoint D p
  disjoint G i
  disjoint G y
  disjoint R f
  disjoint R i
  disjoint R m
  disjoint R n
  disjoint R p
  disjoint R y
  disjoint et f
  disjoint et i
  disjoint f x
  disjoint m x
  disjoint n x
  disjoint p x
  disjoint i ph'
  disjoint p ph'
  disjoint m ph
  disjoint p ph
  disjoint m ps
  disjoint p ps
  disjoint p th
  assert |- ( ( R _FrSe A /\ x e. A /\ ch' /\ et ) -> E. f ( G Fn n /\ ph" /\ ps" ) )

  proof
    cA
    cR
    w-bnj15
    #
    vx
    cv
    #
    cA
    wcel
    #
    bnjwchm
    wet
    w-bnj17
    #
    @0
    wta
    wet
    w3a
    #
    cG
    vn
    cv
    #
    wfn
    #
    bnjwphn
    bnjwpsn
    w3a
    vf
    @3
    wta
    wet
    wa
    #
    @0
    wa
    #
    vf
    @4
    @3
    @7
    vf
    wex
    #
    @0
    @8
    vf
    wex
    @3
    wta
    vf
    wex
    #
    wet
    @9
    @0
    @2
    wa
    #
    bnjwchm
    wa
    #
    wet
    @10
    @3
    @0
    @2
    bnjwchm
    wet
    bnj248
    @12
    vf
    cv
    #
    vm
    cv
    #
    wfn
    bnjwphm
    bnjwpsm
    w3a
    #
    vf
    wta
    bnjwchm
    @11
    @15
    vf
    wex
    #
    bnjwchm
    @11
    @15
    vf
    weu
    #
    @16
    bnjwchm
    @11
    @17
    wi
    wph
    wps
    wch
    vx
    cA
    cR
    vf
    vn
    @14
    bnjwphm
    bnjwpsm
    bnjwchm
    bnj908.4
    bnj908.10
    bnj908.11
    bnj908.12
    vm
    vex
    #
    bnj207
    biimpi
    @15
    vf
    euex
    syl6
    impcom
    bnj908.17
    bnj1198
    bnj832
    @0
    @2
    bnjwchm
    wet
    bnj645
    wta
    wet
    vf
    19.41v
    sylanbrc
    @0
    @2
    bnjwchm
    wet
    bnj642
    @7
    @0
    vf
    19.41v
    sylanbrc
    @0
    wta
    wet
    bnj170
    bnj1198
    @4
    @6
    bnjwphn
    bnjwpsn
    wta
    wet
    wsi
    cA
    cD
    cR
    vm
    vn
    cG
    vp
    bnj908.18
    bnj908.19
    wta
    wsi
    vx
    vy
    cA
    cD
    cR
    vf
    vi
    vm
    vn
    cG
    vp
    bnjwphm
    bnjwpsm
    wph
    cA
    cR
    vn
    @13
    @14
    @1
    bnjwphm
    bnj908.1
    bnj908.10
    @18
    bnj523
    #
    wps
    vy
    cA
    cR
    vi
    vn
    @13
    @14
    bnjwpsm
    bnj908.2
    bnj908.11
    @18
    bnj539
    #
    bnj908.3
    bnj908.16
    bnj908.17
    bnj908.18
    bnj544
    #
    bnj561
    #
    wta
    wet
    wsi
    cA
    cD
    cR
    vm
    vn
    vp
    bnjwphn
    bnj908.18
    bnj908.19
    wta
    wsi
    vx
    vy
    cA
    cD
    cR
    vf
    vm
    vn
    cG
    vp
    bnjwphm
    bnjwpsm
    bnjwphn
    @19
    bnj908.3
    bnj908.16
    bnj908.17
    bnj908.18
    @21
    wph
    cA
    cR
    vf
    cG
    @1
    bnjwphn
    bnj908.1
    bnj908.13
    vy
    cA
    cR
    vf
    vm
    cG
    vp
    bnj908.16
    bnj528
    #
    bnj609
    bnj545
    bnj562
    wta
    wet
    wze
    wsi
    wrh
    vx
    vy
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
    cK
    cL
    vp
    bnjwphm
    bnjwpsm
    bnjwpsn
    bnj908.3
    bnj908.16
    bnj908.17
    bnj908.18
    bnj908.19
    bnj908.20
    bnj908.22
    bnj908.23
    bnj908.24
    bnj908.25
    bnj908.26
    @19
    @20
    @21
    bnj908.21
    @22
    wps
    vy
    cA
    cR
    vf
    vi
    cG
    @5
    bnjwpsn
    bnj908.2
    bnj908.14
    @23
    bnj611
    bnj571
    3jca
    bnj593
end
