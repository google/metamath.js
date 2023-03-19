include "w-bnj15.mm"
include "w-bnj17.mm"
include "cv.mm"
include "csuc.mm"
include "cfv.mm"
include "c-bnj14.mm"
include "ciun.mm"
include "wa.mm"
include "wceq.mm"
include "bnj251.mm"
include "com.mm"
include "wcel.mm"
include "wfn.mm"
include "simp3bi.mm"
include "wne.mm"
include "simp1bi.mm"
include "adantl.mm"
include "bnj563.mm"
include "jca.mm"
include "wi.mm"
include "wal.mm"
include "bnj946.mm"
include "sp.mm"
include "sylbi.mm"
include "imp32.mm"
include "syl2an.mm"
include "simplbiim.mm"
include "wfun.mm"
include "w3a.mm"
include "bnj930.mm"
include "bnj721.mm"
include "wss.mm"
include "cop.mm"
include "csn.mm"
include "bnj931.mm"
include "a1i.mm"
include "cdm.mm"
include "bnj667.mm"
include "bnj564.mm"
include "eleq2.mm"
include "biimpar.mm"
include "3impb.mm"
include "syl.mm"
include "bnj1502.mm"
include "word.mm"
include "bnj252.mm"
include "simplbi.mm"
include "c0.mm"
include "cdif.mm"
include "eldifi.mm"
include "eleq2s.mm"
include "nnord.mm"
include "3syl.mm"
include "adantr.mm"
include "anim12i.mm"
include "fndm.mm"
include "elelsuc.mm"
include "ordsucelsuc.mm"
include "sylan2.mm"
include "iuneq1d.mm"
include "3eqtr4d.mm"
include "syl6eqr.mm"

theorem bnj570
  let wta: wff ta
  let wet: wff et
  let wrh: wff rh
  let vy: setvar y
  let cA: class A
  let cC: class C
  let cD: class D
  let cR: class R
  let vf: setvar f
  let vi: setvar i
  let vm: setvar m
  let vn: setvar n
  let cG: class G
  let cK: class K
  let vp: setvar p
  let bnjwphm: wff ph'
  let bnjwpsm: wff ps'
  assume bnj570.3: |- D = ( _om \ { (/) } )
  assume bnj570.17: |- ( ta <-> ( f Fn m /\ ph' /\ ps' ) )
  assume bnj570.19: |- ( et <-> ( m e. D /\ n = suc m /\ p e. _om /\ m = suc p ) )
  assume bnj570.21: |- ( rh <-> ( i e. _om /\ suc i e. n /\ m =/= suc i ) )
  assume bnj570.24: |- K = U_ y e. ( G ` i ) _pred ( y , A , R )
  assume bnj570.26: |- G = ( f u. { <. m , C >. } )
  assume bnj570.40: |- ( ( R _FrSe A /\ ta /\ et ) -> G Fn n )
  assume bnj570.30: |- ( ps' <-> A. i e. _om ( suc i e. m -> ( f ` suc i ) = U_ y e. ( f ` i ) _pred ( y , A , R ) ) )

  disjoint G y
  disjoint f y
  disjoint i y
  assert |- ( ( R _FrSe A /\ ta /\ et /\ rh ) -> ( G ` suc i ) = K )

  proof
    cA
    cR
    w-bnj15
    #
    wta
    wet
    wrh
    w-bnj17
    #
    vi
    cv
    #
    csuc
    #
    cG
    cfv
    #
    vy
    @2
    cG
    cfv
    #
    cA
    cR
    vy
    cv
    c-bnj14
    #
    ciun
    #
    cK
    @1
    @3
    vf
    cv
    #
    cfv
    #
    vy
    @2
    @8
    cfv
    #
    @6
    ciun
    #
    @4
    @7
    @1
    @0
    wta
    wet
    wrh
    wa
    #
    wa
    #
    @9
    @11
    wceq
    #
    @0
    wta
    wet
    wrh
    bnj251
    wta
    bnjwpsm
    @2
    com
    wcel
    #
    @3
    vm
    cv
    #
    wcel
    #
    wa
    @14
    @12
    wta
    @8
    @16
    wfn
    #
    bnjwphm
    bnjwpsm
    bnj570.17
    simp3bi
    @12
    @15
    @17
    wrh
    @15
    wet
    wrh
    @15
    @3
    vn
    cv
    #
    wcel
    @16
    @3
    wne
    bnj570.21
    simp1bi
    adantl
    wet
    wrh
    cD
    vi
    vm
    vn
    vp
    bnj570.19
    bnj570.21
    bnj563
    #
    jca
    bnjwpsm
    @15
    @17
    @14
    bnjwpsm
    @15
    @17
    @14
    wi
    #
    wi
    #
    vi
    wal
    @22
    bnjwpsm
    @21
    vi
    com
    bnj570.30
    bnj946
    @22
    vi
    sp
    sylbi
    imp32
    syl2an
    simplbiim
    @1
    @3
    cG
    @8
    @0
    wta
    wet
    wrh
    cG
    wfun
    @0
    wta
    wet
    w3a
    @19
    cG
    bnj570.40
    bnj930
    bnj721
    #
    @8
    cG
    wss
    @1
    cG
    @8
    @16
    cC
    cop
    csn
    bnj570.26
    bnj931
    a1i
    #
    @1
    wta
    wet
    wrh
    w3a
    #
    @3
    @8
    cdm
    #
    wcel
    #
    @0
    wta
    wet
    wrh
    bnj667
    #
    wta
    wet
    wrh
    @27
    wta
    @26
    @16
    wceq
    #
    @17
    @27
    @12
    wta
    vf
    vm
    bnjwphm
    bnjwpsm
    bnj570.17
    bnj564
    @20
    @29
    @27
    @17
    @26
    @16
    @3
    eleq2
    biimpar
    syl2an
    3impb
    syl
    bnj1502
    @1
    vy
    @5
    @10
    @6
    @1
    @2
    cG
    @8
    @23
    @24
    @1
    @25
    @2
    @26
    wcel
    #
    @28
    wta
    wet
    wrh
    @30
    @13
    @18
    @16
    word
    #
    @17
    wa
    #
    wa
    @29
    @2
    @16
    wcel
    #
    wa
    @30
    wta
    @18
    @12
    @32
    wta
    @18
    bnjwphm
    bnjwpsm
    bnj570.17
    simp1bi
    @12
    @31
    @17
    wet
    @31
    wrh
    wet
    @16
    cD
    wcel
    #
    @16
    com
    wcel
    #
    @31
    wet
    @34
    @19
    @16
    csuc
    #
    wceq
    #
    vp
    cv
    #
    com
    wcel
    #
    @16
    @38
    csuc
    wceq
    #
    w-bnj17
    #
    @34
    bnj570.19
    @41
    @34
    @37
    @39
    @40
    w3a
    @34
    @37
    @39
    @40
    bnj252
    simplbi
    sylbi
    @35
    @16
    com
    c0
    csn
    #
    cdif
    cD
    @16
    com
    @42
    eldifi
    bnj570.3
    eleq2s
    @16
    nnord
    3syl
    adantr
    @20
    jca
    anim12i
    @18
    @29
    @32
    @33
    @16
    @8
    fndm
    @17
    @31
    @3
    @36
    wcel
    #
    @33
    @3
    @16
    elelsuc
    @31
    @33
    @43
    @2
    @16
    ordsucelsuc
    biimpar
    sylan2
    anim12i
    @29
    @30
    @33
    @26
    @16
    @2
    eleq2
    biimpar
    3syl
    3impb
    syl
    bnj1502
    iuneq1d
    3eqtr4d
    bnj570.24
    syl6eqr
end
