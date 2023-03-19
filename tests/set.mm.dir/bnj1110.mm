include "cv.mm"
include "c0.mm"
include "wne.mm"
include "w3a.mm"
include "wa.mm"
include "cdm.mm"
include "wcel.mm"
include "wel.mm"
include "wb.mm"
include "csuc.mm"
include "wceq.mm"
include "cep.mm"
include "wbr.mm"
include "w-bnj17.mm"
include "cfv.mm"
include "wss.mm"
include "wi.mm"
include "wex.mm"
include "bnj1098.mm"
include "bnj219.mm"
include "adantl.mm"
include "ancli.mm"
include "df-3an.mm"
include "sylibr.mm"
include "bnj1023.mm"
include "wfn.mm"
include "bnj1232.mm"
include "3ad2ant3.mm"
include "anim12ci.mm"
include "anim2i.mm"
include "3anass.mm"
include "bnj1101.mm"
include "3simpb.mm"
include "bnj1235.mm"
include "ad2antll.mm"
include "sylib.mm"
include "syl5.mm"
include "a2i.mm"
include "pm3.43.mm"
include "mpdan.mm"
include "bnj101.mm"
include "bnj1247.mm"
include "pm3.43i.mm"
include "ax-mp.mm"
include "fndm.mm"
include "bnj770.mm"
include "ad2antrl.mm"
include "eleq2d.mm"
include "bnj268.mm"
include "bnj251.mm"
include "bitr3i.mm"
include "imbi2i.mm"
include "exbii.mm"
include "mpbir.mm"
include "simp1.mm"
include "bnj706.mm"
include "simp2.mm"
include "bnj258.mm"
include "simprbi.mm"
include "bnj642.mm"
include "mpbird.mm"
include "bnj645.mm"
include "mp2and.mm"
include "3jca.mm"

theorem bnj1110
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wsi: wff si
  let cB: class B
  let cD: class D
  let vf: setvar f
  let vi: setvar i
  let vj: setvar j
  let vn: setvar n
  let cK: class K
  let bnjwetm: wff et'
  let bnjwph0: wff ph0
  assume bnj1110.3: |- ( ch <-> ( n e. D /\ f Fn n /\ ph /\ ps ) )
  assume bnj1110.7: |- D = ( _om \ { (/) } )
  assume bnj1110.18: |- ( si <-> ( ( j e. n /\ j _E i ) -> et' ) )
  assume bnj1110.19: |- ( ph0 <-> ( i e. n /\ si /\ f e. K /\ i e. dom f ) )
  assume bnj1110.26: |- ( et' <-> ( ( f e. K /\ j e. dom f ) -> ( f ` j ) C_ B ) )

  disjoint D j
  disjoint i j
  disjoint j n
  assert |- E. j ( ( i =/= (/) /\ ( ( th /\ ta /\ ch ) /\ ph0 ) ) -> ( j e. n /\ i = suc j /\ ( f ` j ) C_ B ) )

  proof
    vi
    cv
    #
    c0
    wne
    #
    wth
    wta
    wch
    w3a
    #
    bnjwph0
    wa
    #
    wa
    #
    vj
    cv
    #
    vf
    cv
    #
    cdm
    #
    wcel
    #
    vj
    vn
    wel
    #
    wb
    #
    @9
    @0
    @5
    csuc
    wceq
    #
    @5
    @0
    cep
    wbr
    #
    w3a
    #
    @6
    cK
    wcel
    #
    bnjwetm
    w-bnj17
    #
    @9
    @11
    @5
    @6
    cfv
    cB
    wss
    #
    w3a
    vj
    @4
    @15
    wi
    #
    vj
    wex
    @4
    @10
    @14
    @13
    bnjwetm
    wa
    #
    wa
    #
    wa
    #
    wi
    #
    vj
    wex
    @4
    @19
    wi
    #
    @21
    vj
    @4
    @18
    wi
    #
    @22
    vj
    @4
    @13
    wi
    #
    @23
    vj
    @1
    vi
    vn
    wel
    #
    vn
    cv
    #
    cD
    wcel
    #
    w3a
    #
    @13
    @4
    vj
    @28
    @9
    @11
    wa
    #
    @13
    vj
    cD
    vi
    vj
    vn
    bnj1110.7
    bnj1098
    @29
    @29
    @12
    wa
    @13
    @29
    @12
    @11
    @12
    @9
    vj
    vi
    bnj219
    adantl
    ancli
    @9
    @11
    @12
    df-3an
    sylibr
    bnj1023
    @4
    @1
    @25
    @27
    wa
    #
    wa
    @28
    @3
    @30
    @1
    @2
    @27
    bnjwph0
    @25
    wch
    wth
    @27
    wta
    wch
    @27
    @6
    @26
    wfn
    #
    wph
    wps
    bnj1110.3
    bnj1232
    3ad2ant3
    bnjwph0
    @25
    wsi
    @14
    @0
    @7
    wcel
    #
    bnj1110.19
    bnj1232
    anim12ci
    anim2i
    @1
    @25
    @27
    3anass
    sylibr
    bnj1101
    @24
    @4
    bnjwetm
    wi
    @23
    @4
    @13
    bnjwetm
    @13
    @9
    @12
    wa
    #
    @4
    bnjwetm
    @9
    @11
    @12
    3simpb
    @4
    wsi
    @33
    bnjwetm
    wi
    bnjwph0
    wsi
    @1
    @2
    bnjwph0
    @25
    wsi
    @14
    @32
    bnj1110.19
    bnj1235
    ad2antll
    bnj1110.18
    sylib
    syl5
    a2i
    @4
    @13
    bnjwetm
    pm3.43
    mpdan
    bnj101
    @4
    @14
    wi
    @23
    @22
    wi
    bnjwph0
    @14
    @1
    @2
    bnjwph0
    @25
    wsi
    @14
    @32
    bnj1110.19
    bnj1247
    ad2antll
    @4
    @14
    @18
    pm3.43i
    ax-mp
    bnj101
    @4
    @10
    wi
    @22
    @21
    wi
    @4
    @7
    @26
    @5
    @2
    @7
    @26
    wceq
    #
    @1
    bnjwph0
    wch
    wth
    @34
    wta
    @27
    @31
    wph
    wps
    @34
    wch
    bnj1110.3
    @26
    @6
    fndm
    bnj770
    3ad2ant3
    ad2antrl
    eleq2d
    @4
    @10
    @19
    pm3.43i
    ax-mp
    bnj101
    @17
    @21
    vj
    @15
    @20
    @4
    @15
    @10
    @14
    @13
    bnjwetm
    w-bnj17
    @20
    @10
    @14
    @13
    bnjwetm
    bnj268
    @10
    @14
    @13
    bnjwetm
    bnj251
    bitr3i
    imbi2i
    exbii
    mpbir
    @15
    @9
    @11
    @16
    @10
    @13
    @14
    bnjwetm
    @9
    @9
    @11
    @12
    simp1
    bnj706
    #
    @10
    @13
    @14
    bnjwetm
    @11
    @9
    @11
    @12
    simp2
    bnj706
    @15
    @14
    @8
    @16
    @15
    @10
    @13
    bnjwetm
    w3a
    @14
    @10
    @13
    @14
    bnjwetm
    bnj258
    simprbi
    @15
    @8
    @9
    @35
    @10
    @13
    @14
    bnjwetm
    bnj642
    mpbird
    @15
    bnjwetm
    @14
    @8
    wa
    @16
    wi
    @10
    @13
    @14
    bnjwetm
    bnj645
    bnj1110.26
    sylib
    mp2and
    3jca
    bnj1023
end
