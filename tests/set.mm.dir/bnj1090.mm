include "w-bnj17.mm"
include "cv.mm"
include "cfv.mm"
include "wss.mm"
include "wi.mm"
include "wex.mm"
include "wal.mm"
include "wral.mm"
include "wel.mm"
include "wcel.mm"
include "cdm.mm"
include "wa.mm"
include "impexp.mm"
include "exbii.mm"
include "cep.mm"
include "wbr.mm"
include "imbi1i.mm"
include "imbi2i.mm"
include "19.37v.mm"
include "wsbc.mm"
include "bnj115.mm"
include "albii.mm"
include "bitr4i.mm"
include "19.36v.mm"
include "3bitr4i.mm"
include "bitr2i.mm"
include "bnj256.mm"
include "bnj133.mm"
include "df-ral.mm"
include "sylibr.mm"

theorem bnj1090
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let wze: wff ze
  let wsi: wff si
  let wrh: wff rh
  let cB: class B
  let vf: setvar f
  let vi: setvar i
  let vj: setvar j
  let vn: setvar n
  let cK: class K
  let bnjwetm: wff et'
  let bnjwph0: wff ph0
  assume bnj1090.9: |- ( et <-> ( ( f e. K /\ i e. dom f ) -> ( f ` i ) C_ B ) )
  assume bnj1090.10: |- ( rh <-> A. j e. n ( j _E i -> [. j / i ]. et ) )
  assume bnj1090.17: |- ( et' <-> [. j / i ]. et )
  assume bnj1090.18: |- ( si <-> ( ( j e. n /\ j _E i ) -> et' ) )
  assume bnj1090.19: |- ( ph0 <-> ( i e. n /\ si /\ f e. K /\ i e. dom f ) )
  assume bnj1090.28: |- ( ( th /\ ta /\ ch /\ ze ) -> A. i E. j ( ph0 -> ( f ` i ) C_ B ) )

  disjoint et j
  disjoint i j
  disjoint j n
  assert |- ( ( th /\ ta /\ ch /\ ze ) -> A. i e. n ( rh -> et ) )

  proof
    wth
    wta
    wch
    wze
    w-bnj17
    bnjwph0
    vi
    cv
    #
    vf
    cv
    #
    cfv
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
    #
    wrh
    wet
    wi
    #
    vi
    vn
    cv
    #
    wral
    #
    bnj1090.28
    vi
    vn
    wel
    #
    @6
    wi
    #
    vi
    wal
    @9
    wsi
    @1
    cK
    wcel
    #
    @0
    @1
    cdm
    wcel
    #
    w-bnj17
    #
    @2
    wi
    #
    vj
    wex
    #
    vi
    wal
    @8
    @5
    @10
    @15
    vi
    @10
    @9
    wsi
    wa
    #
    wet
    wi
    #
    @14
    vj
    @17
    vj
    wex
    @9
    wsi
    wet
    wi
    #
    wi
    #
    vj
    wex
    #
    @10
    @17
    @19
    vj
    @9
    wsi
    wet
    impexp
    exbii
    @9
    @18
    vj
    wex
    #
    wi
    @9
    vj
    vn
    wel
    vj
    cv
    #
    @0
    cep
    wbr
    #
    wa
    #
    bnjwetm
    wi
    #
    wet
    wi
    #
    vj
    wex
    #
    wi
    @20
    @10
    @21
    @27
    @9
    @18
    @26
    vj
    wsi
    @25
    wet
    bnj1090.18
    imbi1i
    exbii
    imbi2i
    @9
    @18
    vj
    19.37v
    @6
    @27
    @9
    @6
    @25
    vj
    wal
    #
    wet
    wi
    @27
    wrh
    @28
    wet
    wrh
    @24
    wet
    vi
    @22
    wsbc
    #
    wi
    #
    vj
    wal
    @28
    @29
    @23
    wrh
    @7
    vj
    bnj1090.10
    bnj115
    @25
    @30
    vj
    bnjwetm
    @29
    @24
    bnj1090.17
    imbi2i
    albii
    bitr4i
    imbi1i
    @25
    wet
    vj
    19.36v
    bitr4i
    imbi2i
    3bitr4i
    bitr2i
    @16
    @11
    @12
    wa
    #
    wa
    #
    @2
    wi
    @16
    @31
    @2
    wi
    #
    wi
    @14
    @17
    @16
    @31
    @2
    impexp
    @13
    @32
    @2
    @9
    wsi
    @11
    @12
    bnj256
    imbi1i
    wet
    @33
    @16
    bnj1090.9
    imbi2i
    3bitr4i
    bnj133
    albii
    @6
    vi
    @7
    df-ral
    @4
    @15
    vi
    @3
    @14
    vj
    bnjwph0
    @13
    @2
    bnj1090.19
    imbi1i
    exbii
    albii
    3bitr4i
    sylibr
end
