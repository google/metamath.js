include "word.mm"
include "wtr.mm"
include "cv.mm"
include "wral.mm"
include "wa.mm"
include "wcel.mm"
include "wel.mm"
include "wi.mm"
include "wal.mm"
include "dford3.mm"
include "dftr2.mm"
include "19.3v.mm"
include "ancom.mm"
include "imbi1i.mm"
include "bitri.mm"
include "2albii.mm"
include "alcom.mm"
include "bitr4i.mm"
include "df-ral.mm"
include "imbi2i.mm"
include "nfv.mm"
include "19.21-2.mm"
include "impexp.mm"
include "anbi2i.mm"
include "anass.mm"
include "bitr3i.mm"
include "3bitri.mm"
include "albii.mm"
include "anbi12i.mm"
include "19.26.mm"
include "19.26-2.mm"
include "pm4.76.mm"

theorem dford4
  let cN: class N
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vx: setvar x
  let vy: setvar y

  disjoint a b
  disjoint a c
  disjoint b c
  disjoint N a
  disjoint N b
  disjoint N c
  disjoint a x
  disjoint a y
  disjoint b x
  disjoint b y
  disjoint c x
  disjoint c y
  disjoint x y
  disjoint N x
  disjoint N y
  assert |- ( Ord N <-> A. a A. b A. c ( ( a e. N /\ b e. a ) -> ( b e. N /\ ( c e. b -> c e. a ) ) ) )

  proof
    cN
    word
    cN
    wtr
    #
    va
    cv
    #
    wtr
    #
    va
    cN
    wral
    #
    wa
    #
    @1
    cN
    wcel
    #
    vb
    va
    wel
    #
    wa
    #
    vb
    cv
    cN
    wcel
    #
    wi
    #
    vc
    wal
    #
    vb
    wal
    #
    @7
    vc
    vb
    wel
    #
    vc
    va
    wel
    #
    wi
    #
    wi
    #
    vc
    wal
    vb
    wal
    #
    wa
    #
    va
    wal
    #
    @7
    @8
    @14
    wa
    wi
    #
    vc
    wal
    vb
    wal
    #
    va
    wal
    va
    cN
    dford3
    @4
    @11
    va
    wal
    #
    @16
    va
    wal
    #
    wa
    @18
    @0
    @21
    @3
    @22
    @0
    @6
    @5
    wa
    #
    @8
    wi
    #
    va
    wal
    vb
    wal
    #
    @21
    vb
    va
    cN
    dftr2
    @21
    @24
    vb
    wal
    va
    wal
    @25
    @10
    @24
    va
    vb
    @10
    @9
    @24
    @9
    vc
    19.3v
    @7
    @23
    @8
    @5
    @6
    ancom
    imbi1i
    bitri
    2albii
    @24
    va
    vb
    alcom
    bitri
    bitr4i
    @3
    @5
    @2
    wi
    #
    va
    wal
    @22
    @2
    va
    cN
    df-ral
    @26
    @16
    va
    @26
    @5
    @12
    @6
    wa
    #
    @13
    wi
    #
    wi
    #
    vb
    wal
    vc
    wal
    #
    @15
    vb
    wal
    vc
    wal
    @16
    @26
    @5
    @28
    vb
    wal
    vc
    wal
    #
    wi
    @30
    @2
    @31
    @5
    vc
    vb
    @1
    dftr2
    imbi2i
    @5
    @28
    vc
    vb
    @5
    vc
    nfv
    @5
    vb
    nfv
    19.21-2
    bitr4i
    @29
    @15
    vc
    vb
    @29
    @7
    @12
    wa
    #
    @13
    wi
    #
    @15
    @29
    @5
    @27
    wa
    #
    @13
    wi
    @33
    @5
    @27
    @13
    impexp
    @34
    @32
    @13
    @34
    @5
    @6
    @12
    wa
    #
    wa
    @32
    @27
    @35
    @5
    @12
    @6
    ancom
    anbi2i
    @5
    @6
    @12
    anass
    bitr4i
    imbi1i
    bitr3i
    @7
    @12
    @13
    impexp
    bitri
    2albii
    @15
    vc
    vb
    alcom
    3bitri
    albii
    bitri
    anbi12i
    @11
    @16
    va
    19.26
    bitr4i
    @17
    @20
    va
    @17
    @9
    @15
    wa
    #
    vc
    wal
    vb
    wal
    @20
    @9
    @15
    vb
    vc
    19.26-2
    @36
    @19
    vb
    vc
    @7
    @8
    @14
    pm4.76
    2albii
    bitr3i
    albii
    3bitri
end
