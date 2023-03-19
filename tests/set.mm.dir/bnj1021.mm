include "w-bnj17.mm"
include "wi.mm"
include "wex.mm"
include "w3a.mm"
include "bnj996.mm"
include "wa.mm"
include "anclb.mm"
include "bnj252.mm"
include "imbi2i.mm"
include "bitr4i.mm"
include "2exbii.mm"
include "3exbii.mm"
include "mpbi.mm"
include "19.37v.mm"
include "bnj1019.mm"
include "bitri.mm"

theorem bnj1021
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
  let cD: class D
  let cR: class R
  let vf: setvar f
  let vi: setvar i
  let vm: setvar m
  let vn: setvar n
  let cX: class X
  let vp: setvar p
  assume bnj1021.1: |- ( ph <-> ( f ` (/) ) = _pred ( X , A , R ) )
  assume bnj1021.2: |- ( ps <-> A. i e. _om ( suc i e. n -> ( f ` suc i ) = U_ y e. ( f ` i ) _pred ( y , A , R ) ) )
  assume bnj1021.3: |- ( ch <-> ( n e. D /\ f Fn n /\ ph /\ ps ) )
  assume bnj1021.4: |- ( th <-> ( R _FrSe A /\ X e. A /\ y e. _trCl ( X , A , R ) /\ z e. _pred ( y , A , R ) ) )
  assume bnj1021.5: |- ( ta <-> ( m e. _om /\ n = suc m /\ p = suc n ) )
  assume bnj1021.6: |- ( et <-> ( i e. n /\ y e. ( f ` i ) ) )
  assume bnj1021.13: |- D = ( _om \ { (/) } )
  assume bnj1021.14: |- B = { f | E. n e. D ( f Fn n /\ ph /\ ps ) }

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
  disjoint ch m
  disjoint ch p
  disjoint m p
  disjoint et m
  disjoint et p
  disjoint f th
  disjoint i th
  disjoint n th
  disjoint i ph
  disjoint m n
  disjoint m th
  disjoint n p
  disjoint p th
  assert |- E. f E. n E. i E. m ( th -> ( th /\ ch /\ et /\ E. p ta ) )

  proof
    wth
    wth
    wch
    wta
    wet
    w-bnj17
    #
    wi
    #
    vp
    wex
    #
    vm
    wex
    #
    vi
    wex
    #
    vn
    wex
    vf
    wex
    #
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
    vi
    wex
    #
    vn
    wex
    vf
    wex
    wth
    wch
    wta
    wet
    w3a
    #
    wi
    #
    vp
    wex
    vm
    wex
    #
    vi
    wex
    vn
    wex
    vf
    wex
    @5
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
    bnj1021.1
    bnj1021.2
    bnj1021.3
    bnj1021.4
    bnj1021.5
    bnj1021.6
    bnj1021.13
    bnj1021.14
    bnj996
    @11
    @3
    vf
    vn
    vi
    @10
    @1
    vm
    vp
    @10
    wth
    wth
    @9
    wa
    #
    wi
    @1
    wth
    @9
    anclb
    @0
    @12
    wth
    wth
    wch
    wta
    wet
    bnj252
    imbi2i
    bitr4i
    2exbii
    3exbii
    mpbi
    @4
    @8
    vf
    vn
    @2
    @7
    vi
    vm
    @2
    wth
    @0
    vp
    wex
    #
    wi
    @7
    wth
    @0
    vp
    19.37v
    @13
    @6
    wth
    wch
    wth
    wta
    wet
    vp
    bnj1019
    imbi2i
    bitri
    2exbii
    2exbii
    mpbi
end
