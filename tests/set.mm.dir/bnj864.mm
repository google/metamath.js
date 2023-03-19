include "w-bnj15.mm"
include "wcel.mm"
include "cv.mm"
include "w3a.mm"
include "wfn.mm"
include "weu.mm"
include "wi.mm"
include "wa.mm"
include "wral.mm"
include "wal.mm"
include "bnj852.mm"
include "df-ral.mm"
include "imbi2i.mm"
include "19.21v.mm"
include "impexp.mm"
include "df-3an.mm"
include "bicomi.mm"
include "imbi1i.mm"
include "bitr3i.mm"
include "albii.mm"
include "3bitr2i.mm"
include "mpbi.mm"
include "spi.mm"
include "eubii.mm"
include "3imtr4i.mm"

theorem bnj864
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let vy: setvar y
  let cA: class A
  let cD: class D
  let cR: class R
  let vf: setvar f
  let vi: setvar i
  let vn: setvar n
  let cX: class X
  assume bnj864.1: |- ( ph <-> ( f ` (/) ) = _pred ( X , A , R ) )
  assume bnj864.2: |- ( ps <-> A. i e. _om ( suc i e. n -> ( f ` suc i ) = U_ y e. ( f ` i ) _pred ( y , A , R ) ) )
  assume bnj864.3: |- D = ( _om \ { (/) } )
  assume bnj864.4: |- ( ch <-> ( R _FrSe A /\ X e. A /\ n e. D ) )
  assume bnj864.5: |- ( th <-> ( f Fn n /\ ph /\ ps ) )

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
  disjoint D f
  disjoint D i
  disjoint D n
  disjoint R f
  disjoint R i
  disjoint R n
  disjoint R y
  disjoint X f
  disjoint X n
  assert |- ( ch -> E! f th )

  proof
    cA
    cR
    w-bnj15
    #
    cX
    cA
    wcel
    #
    vn
    cv
    #
    cD
    wcel
    #
    w3a
    #
    vf
    cv
    @2
    wfn
    wph
    wps
    w3a
    #
    vf
    weu
    #
    wch
    wth
    vf
    weu
    @4
    @6
    wi
    #
    vn
    @0
    @1
    wa
    #
    @6
    vn
    cD
    wral
    #
    wi
    #
    @7
    vn
    wal
    #
    wph
    wps
    vy
    cA
    cD
    cR
    vf
    vi
    vn
    cX
    bnj864.1
    bnj864.2
    bnj864.3
    bnj852
    @10
    @8
    @3
    @6
    wi
    #
    vn
    wal
    #
    wi
    @8
    @12
    wi
    #
    vn
    wal
    @11
    @9
    @13
    @8
    @6
    vn
    cD
    df-ral
    imbi2i
    @8
    @12
    vn
    19.21v
    @14
    @7
    vn
    @14
    @8
    @3
    wa
    #
    @6
    wi
    @7
    @8
    @3
    @6
    impexp
    @15
    @4
    @6
    @4
    @15
    @0
    @1
    @3
    df-3an
    bicomi
    imbi1i
    bitr3i
    albii
    3bitr2i
    mpbi
    spi
    bnj864.4
    wth
    @5
    vf
    bnj864.5
    eubii
    3imtr4i
end
