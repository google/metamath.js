include "w-bnj17.mm"
include "cv.mm"
include "wcel.mm"
include "wi.mm"
include "wal.mm"
include "wex.mm"
include "19.23vv.mm"
include "albii.mm"
include "19.23v.mm"
include "bitri.mm"
include "cep.mm"
include "wfr.mm"
include "wral.mm"
include "wa.mm"
include "vex.mm"
include "bnj110.mm"
include "bnj1049.mm"
include "sylib.mm"
include "19.21bi.mm"
include "mpcom.mm"
include "gen2.mm"
include "mpgbi.mm"
include "bnj1034.mm"

theorem bnj1052
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let wze: wff ze
  let wrh: wff rh
  let vy: setvar y
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let vf: setvar f
  let vi: setvar i
  let vj: setvar j
  let vn: setvar n
  let cK: class K
  let cX: class X
  assume bnj1052.1: |- ( ph <-> ( f ` (/) ) = _pred ( X , A , R ) )
  assume bnj1052.2: |- ( ps <-> A. i e. _om ( suc i e. n -> ( f ` suc i ) = U_ y e. ( f ` i ) _pred ( y , A , R ) ) )
  assume bnj1052.3: |- ( ch <-> ( n e. D /\ f Fn n /\ ph /\ ps ) )
  assume bnj1052.4: |- ( th <-> ( R _FrSe A /\ X e. A ) )
  assume bnj1052.5: |- ( ta <-> ( B e. _V /\ _TrFo ( B , A , R ) /\ _pred ( X , A , R ) C_ B ) )
  assume bnj1052.6: |- ( ze <-> ( i e. n /\ z e. ( f ` i ) ) )
  assume bnj1052.7: |- D = ( _om \ { (/) } )
  assume bnj1052.8: |- K = { f | E. n e. D ( f Fn n /\ ph /\ ps ) }
  assume bnj1052.9: |- ( et <-> ( ( th /\ ta /\ ch /\ ze ) -> z e. B ) )
  assume bnj1052.10: |- ( rh <-> A. j e. n ( j _E i -> [. j / i ]. et ) )
  assume bnj1052.37: |- ( ( th /\ ta /\ ch /\ ze ) -> ( _E Fr n /\ A. i e. n ( rh -> et ) ) )

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
  disjoint A z
  disjoint f z
  disjoint i z
  disjoint n z
  disjoint B f
  disjoint B i
  disjoint B n
  disjoint B z
  disjoint D i
  disjoint R f
  disjoint R i
  disjoint R n
  disjoint R y
  disjoint R z
  disjoint X f
  disjoint X i
  disjoint X n
  disjoint X y
  disjoint X z
  disjoint et j
  disjoint f ta
  disjoint i ta
  disjoint n ta
  disjoint ta z
  disjoint f th
  disjoint i th
  disjoint n th
  disjoint th z
  disjoint i j
  disjoint j n
  disjoint i ph
  assert |- ( ( th /\ ta ) -> _trCl ( X , A , R ) C_ B )

  proof
    wph
    wps
    wch
    wth
    wta
    wze
    vy
    vz
    cA
    cB
    cD
    cR
    vf
    vi
    vn
    cK
    cX
    bnj1052.1
    bnj1052.2
    bnj1052.3
    bnj1052.4
    bnj1052.5
    bnj1052.6
    bnj1052.7
    bnj1052.8
    wth
    wta
    wch
    wze
    w-bnj17
    #
    vz
    cv
    cB
    wcel
    #
    wi
    #
    vi
    wal
    vn
    wal
    #
    @0
    vi
    wex
    vn
    wex
    #
    vf
    wex
    @1
    wi
    #
    vf
    @3
    vf
    wal
    @4
    @1
    wi
    #
    vf
    wal
    @5
    @3
    @6
    vf
    @0
    @1
    vn
    vi
    19.23vv
    albii
    @4
    @1
    vf
    19.23v
    bitri
    @2
    vn
    vi
    vn
    cv
    #
    cep
    wfr
    wrh
    wet
    wi
    vi
    @7
    wral
    wa
    #
    @0
    @1
    bnj1052.37
    @8
    wet
    @2
    @8
    wet
    vi
    @8
    wet
    vi
    @7
    wral
    wet
    vi
    wal
    wet
    wrh
    vi
    vj
    @7
    cep
    vn
    vex
    bnj1052.10
    bnj110
    wch
    wth
    wta
    wet
    wze
    vz
    cB
    vf
    vi
    vn
    bnj1052.6
    bnj1052.9
    bnj1049
    sylib
    19.21bi
    bnj1052.9
    sylib
    mpcom
    gen2
    mpgbi
    bnj1034
end
