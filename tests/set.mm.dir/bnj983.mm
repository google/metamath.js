include "c-bnj18.mm"
include "wcel.mm"
include "cv.mm"
include "cdm.mm"
include "cfv.mm"
include "wa.mm"
include "wex.mm"
include "w3a.mm"
include "wfn.mm"
include "wrex.mm"
include "ciun.mm"
include "bnj882.mm"
include "eleq2i.mm"
include "eliun.mm"
include "rexbii.mm"
include "bitri.mm"
include "df-rex.mm"
include "abeq2i.mm"
include "anbi1i.mm"
include "exbii.mm"
include "3bitri.mm"
include "w-bnj17.mm"
include "bnj252.mm"
include "anbi12i.mm"
include "bitr4i.mm"
include "bnj133.mm"
include "19.41v.mm"
include "csuc.mm"
include "c-bnj14.mm"
include "wceq.mm"
include "wi.mm"
include "com.mm"
include "bnj1095.mm"
include "bnj1096.mm"
include "nf5i.mm"
include "19.42.mm"
include "2exbii.mm"
include "3anass.mm"
include "3exbii.mm"
include "wb.mm"
include "fndm.mm"
include "bnj770.mm"
include "eleq2.mm"
include "3anbi2d.mm"
include "syl.mm"
include "3ad2ant1.mm"
include "ibi.mm"
include "ibir.mm"
include "impbii.mm"
include "3bitr2i.mm"

theorem bnj983
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
  let cZ: class Z
  assume bnj983.1: |- ( ph <-> ( f ` (/) ) = _pred ( X , A , R ) )
  assume bnj983.2: |- ( ps <-> A. i e. _om ( suc i e. n -> ( f ` suc i ) = U_ y e. ( f ` i ) _pred ( y , A , R ) ) )
  assume bnj983.3: |- D = ( _om \ { (/) } )
  assume bnj983.4: |- B = { f | E. n e. D ( f Fn n /\ ph /\ ps ) }
  assume bnj983.5: |- ( ch <-> ( n e. D /\ f Fn n /\ ph /\ ps ) )

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
  disjoint Z f
  disjoint Z i
  disjoint Z n
  disjoint i ph
  assert |- ( Z e. _trCl ( X , A , R ) <-> E. f E. n E. i ( ch /\ i e. n /\ Z e. ( f ` i ) ) )

  proof
    cZ
    cA
    cR
    cX
    c-bnj18
    #
    wcel
    #
    wch
    vi
    cv
    #
    vf
    cv
    #
    cdm
    #
    wcel
    #
    cZ
    @2
    @3
    cfv
    #
    wcel
    #
    wa
    #
    wa
    #
    vi
    wex
    #
    vn
    wex
    vf
    wex
    #
    wch
    @5
    @7
    w3a
    #
    vi
    wex
    vn
    wex
    vf
    wex
    wch
    @2
    vn
    cv
    #
    wcel
    #
    @7
    w3a
    #
    vi
    wex
    vn
    wex
    vf
    wex
    @1
    wch
    @8
    vi
    wex
    #
    wa
    #
    vn
    wex
    #
    vf
    wex
    @11
    @1
    wch
    vn
    wex
    #
    @16
    wa
    #
    @18
    vf
    @1
    @3
    @13
    wfn
    #
    wph
    wps
    w3a
    #
    vn
    cD
    wrex
    #
    @7
    vi
    @4
    wrex
    #
    wa
    #
    @20
    vf
    @1
    cZ
    vf
    cB
    vi
    @4
    @6
    ciun
    #
    ciun
    #
    wcel
    #
    @24
    vf
    cB
    wrex
    #
    @25
    vf
    wex
    #
    @0
    @27
    cZ
    wph
    wps
    vy
    cA
    cB
    cD
    cR
    vf
    vi
    vn
    cX
    bnj983.1
    bnj983.2
    bnj983.3
    bnj983.4
    bnj882
    eleq2i
    @28
    cZ
    @26
    wcel
    #
    vf
    cB
    wrex
    @29
    vf
    cZ
    cB
    @26
    eliun
    @31
    @24
    vf
    cB
    vi
    cZ
    @4
    @6
    eliun
    rexbii
    bitri
    @29
    @3
    cB
    wcel
    #
    @24
    wa
    #
    vf
    wex
    @30
    @24
    vf
    cB
    df-rex
    @33
    @25
    vf
    @32
    @23
    @24
    @23
    vf
    cB
    bnj983.4
    abeq2i
    anbi1i
    exbii
    bitri
    3bitri
    @20
    @13
    cD
    wcel
    #
    @22
    wa
    #
    vn
    wex
    #
    @16
    wa
    @25
    @19
    @36
    @16
    wch
    @35
    vn
    wch
    @34
    @21
    wph
    wps
    w-bnj17
    @35
    bnj983.5
    @34
    @21
    wph
    wps
    bnj252
    bitri
    exbii
    anbi1i
    @23
    @36
    @24
    @16
    @22
    vn
    cD
    df-rex
    @7
    vi
    @4
    df-rex
    anbi12i
    bitr4i
    bnj133
    wch
    @16
    vn
    19.41v
    bnj133
    @10
    @17
    vf
    vn
    wch
    @8
    vi
    wch
    vi
    wps
    wch
    @34
    @21
    wph
    vi
    wps
    @2
    csuc
    #
    @13
    wcel
    @37
    @3
    cfv
    vy
    @6
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
    bnj983.2
    bnj1095
    bnj983.5
    bnj1096
    nf5i
    19.42
    2exbii
    bitr4i
    @12
    @9
    vf
    vn
    vi
    wch
    @5
    @7
    3anass
    3exbii
    @12
    @15
    vf
    vn
    vi
    @12
    @15
    @12
    @15
    wch
    @5
    @12
    @15
    wb
    #
    @7
    wch
    @4
    @13
    wceq
    #
    @38
    @34
    @21
    wph
    wps
    @39
    wch
    bnj983.5
    @13
    @3
    fndm
    bnj770
    @39
    @5
    @14
    wch
    @7
    @4
    @13
    @2
    eleq2
    3anbi2d
    syl
    #
    3ad2ant1
    ibi
    @15
    @12
    wch
    @14
    @38
    @7
    @40
    3ad2ant1
    ibir
    impbii
    3exbii
    3bitr2i
end
