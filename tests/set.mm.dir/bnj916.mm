include "cv.mm"
include "c-bnj18.mm"
include "wcel.mm"
include "cdm.mm"
include "cfv.mm"
include "w-bnj17.mm"
include "wex.mm"
include "wfn.mm"
include "w3a.mm"
include "wrex.mm"
include "wa.mm"
include "bnj256.mm"
include "2exbii.mm"
include "19.41v.mm"
include "nfv.mm"
include "bnj911.mm"
include "nf5i.mm"
include "nfan.mm"
include "19.42.mm"
include "exbii.mm"
include "df-rex.mm"
include "anbi12i.mm"
include "3bitr4i.mm"
include "bitri.mm"
include "3anbi2i.mm"
include "anbi1i.mm"
include "df-bnj17.mm"
include "3exbii.mm"
include "ciun.mm"
include "bnj882.mm"
include "eleq2i.mm"
include "eliun.mm"
include "rexbii.mm"
include "3bitri.mm"
include "abeq2i.mm"
include "3bitr4ri.mm"
include "wb.mm"
include "bnj643.mm"
include "bnj564.mm"
include "eleq2d.mm"
include "anbi1.mm"
include "bnj334.mm"
include "bnj252.mm"
include "3bitr4g.mm"
include "3syl.mm"
include "ibi.mm"
include "2eximi.mm"
include "eximi.mm"
include "sylbi.mm"

theorem bnj916
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
  assume bnj916.1: |- ( ph <-> ( f ` (/) ) = _pred ( X , A , R ) )
  assume bnj916.2: |- ( ps <-> A. i e. _om ( suc i e. n -> ( f ` suc i ) = U_ y e. ( f ` i ) _pred ( y , A , R ) ) )
  assume bnj916.3: |- D = ( _om \ { (/) } )
  assume bnj916.4: |- B = { f | E. n e. D ( f Fn n /\ ph /\ ps ) }
  assume bnj916.5: |- ( ch <-> ( f Fn n /\ ph /\ ps ) )

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
  assert |- ( y e. _trCl ( X , A , R ) -> E. f E. n E. i ( n e. D /\ ch /\ i e. n /\ y e. ( f ` i ) ) )

  proof
    vy
    cv
    #
    cA
    cR
    cX
    c-bnj18
    #
    wcel
    #
    vn
    cv
    #
    cD
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
    @0
    @5
    @6
    cfv
    #
    wcel
    #
    w-bnj17
    #
    vi
    wex
    vn
    wex
    #
    vf
    wex
    #
    @4
    wch
    @5
    @3
    wcel
    #
    @10
    w-bnj17
    #
    vi
    wex
    vn
    wex
    #
    vf
    wex
    @4
    @6
    @3
    wfn
    wph
    wps
    w3a
    #
    @8
    @10
    w-bnj17
    #
    vi
    wex
    vn
    wex
    #
    vf
    wex
    @17
    vn
    cD
    wrex
    #
    @10
    vi
    @7
    wrex
    #
    wa
    #
    vf
    wex
    #
    @13
    @2
    @19
    @22
    vf
    @19
    @4
    @17
    wa
    #
    @8
    @10
    wa
    #
    wa
    #
    vi
    wex
    #
    vn
    wex
    #
    @22
    @18
    @26
    vn
    vi
    @4
    @17
    @8
    @10
    bnj256
    2exbii
    @24
    @25
    vi
    wex
    #
    wa
    #
    vn
    wex
    @24
    vn
    wex
    #
    @29
    wa
    @28
    @22
    @24
    @29
    vn
    19.41v
    @27
    @30
    vn
    @24
    @25
    vi
    @4
    @17
    vi
    @4
    vi
    nfv
    @17
    vi
    wph
    wps
    vy
    cA
    cR
    vf
    vi
    vn
    cX
    bnj916.1
    bnj916.2
    bnj911
    nf5i
    nfan
    19.42
    exbii
    @20
    @31
    @21
    @29
    @17
    vn
    cD
    df-rex
    @10
    vi
    @7
    df-rex
    anbi12i
    3bitr4i
    bitri
    exbii
    @11
    @18
    vf
    vn
    vi
    @4
    wch
    @8
    w3a
    #
    @10
    wa
    @4
    @17
    @8
    w3a
    #
    @10
    wa
    @11
    @18
    @32
    @33
    @10
    wch
    @17
    @4
    @8
    bnj916.5
    3anbi2i
    anbi1i
    @4
    wch
    @8
    @10
    df-bnj17
    @4
    @17
    @8
    @10
    df-bnj17
    3bitr4i
    3exbii
    @2
    @21
    vf
    cB
    wrex
    #
    @6
    cB
    wcel
    #
    @21
    wa
    #
    vf
    wex
    @23
    @2
    @0
    vf
    cB
    vi
    @7
    @9
    ciun
    #
    ciun
    #
    wcel
    @0
    @37
    wcel
    #
    vf
    cB
    wrex
    @34
    @1
    @38
    @0
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
    bnj916.1
    bnj916.2
    bnj916.3
    bnj916.4
    bnj882
    eleq2i
    vf
    @0
    cB
    @37
    eliun
    @39
    @21
    vf
    cB
    vi
    @0
    @7
    @9
    eliun
    rexbii
    3bitri
    @21
    vf
    cB
    df-rex
    @36
    @22
    vf
    @35
    @20
    @21
    @20
    vf
    cB
    bnj916.4
    abeq2i
    anbi1i
    exbii
    3bitri
    3bitr4ri
    @12
    @16
    vf
    @11
    @15
    vn
    vi
    @11
    @15
    @11
    wch
    @8
    @14
    wb
    #
    @11
    @15
    wb
    @4
    wch
    @8
    @10
    bnj643
    wch
    @7
    @3
    @5
    wch
    vf
    vn
    wph
    wps
    bnj916.5
    bnj564
    eleq2d
    @40
    @8
    @4
    wch
    @10
    w3a
    #
    wa
    #
    @14
    @41
    wa
    #
    @11
    @15
    @8
    @14
    @41
    anbi1
    @11
    @8
    @4
    wch
    @10
    w-bnj17
    @42
    @4
    wch
    @8
    @10
    bnj334
    @8
    @4
    wch
    @10
    bnj252
    bitri
    @15
    @14
    @4
    wch
    @10
    w-bnj17
    @43
    @4
    wch
    @14
    @10
    bnj334
    @14
    @4
    wch
    @10
    bnj252
    bitri
    3bitr4g
    3syl
    ibi
    2eximi
    eximi
    sylbi
end
