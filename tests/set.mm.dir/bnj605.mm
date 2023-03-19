include "cv.mm"
include "c1o.mm"
include "wne.mm"
include "wcel.mm"
include "w-bnj15.mm"
include "wa.mm"
include "wfn.mm"
include "w3a.mm"
include "wex.mm"
include "wi.mm"
include "anim1i.mm"
include "nfv.mm"
include "19.41.mm"
include "exbii.mm"
include "cep.mm"
include "wbr.mm"
include "wsbc.mm"
include "bnj1095.mm"
include "nf5i.mm"
include "bitr2i.mm"
include "sylib.mm"
include "csuc.mm"
include "wceq.mm"
include "com.mm"
include "bnj1232.mm"
include "bnj219.mm"
include "bnj770.mm"
include "jca.mm"
include "bnj170.mm"
include "sylibr.mm"
include "syl.mm"
include "simpl.mm"
include "2eximi.mm"
include "w-bnj17.mm"
include "bnj248.mm"
include "weu.mm"
include "pm3.35.mm"
include "sylan2b.mm"
include "euex.mm"
include "bnj1198.mm"
include "bnj832.mm"
include "3jca.mm"
include "3com23.mm"
include "3expia.mm"
include "eximdv.mm"
include "adantlr.mm"
include "sylbi.mm"
include "mpd.mm"
include "bnj432.mm"
include "biid.mm"
include "sbcid.mm"
include "bitri.mm"
include "3anbi123i.mm"
include "3imtr3i.mm"
include "ex.mm"
include "exlimivv.mm"
include "3syl.mm"
include "3impa.mm"

theorem bnj605
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cD: class D
  let cR: class R
  let vf: setvar f
  let vi: setvar i
  let vm: setvar m
  let vn: setvar n
  let vp: setvar p
  let bnjwphm: wff ph'
  let bnjwpsm: wff ps'
  let bnjwchm: wff ch'
  let bnjwphn: wff ph"
  let bnjwpsn: wff ps"
  assume bnj605.5: |- ( th <-> A. m e. D ( m _E n -> [. m / n ]. ch ) )
  assume bnj605.13: |- ( ph" <-> [. f / f ]. ph )
  assume bnj605.14: |- ( ps" <-> [. f / f ]. ps )
  assume bnj605.17: |- ( ta <-> ( f Fn m /\ ph' /\ ps' ) )
  assume bnj605.19: |- ( et <-> ( m e. D /\ n = suc m /\ p e. _om /\ m = suc p ) )
  assume bnj605.28: |- f e. _V
  assume bnj605.31: |- ( ch' <-> ( ( R _FrSe A /\ x e. A ) -> E! f ( f Fn m /\ ph' /\ ps' ) ) )
  assume bnj605.32: |- ( ph" <-> ( f ` (/) ) = _pred ( x , A , R ) )
  assume bnj605.33: |- ( ps" <-> A. i e. _om ( suc i e. n -> ( f ` suc i ) = U_ y e. ( f ` i ) _pred ( y , A , R ) ) )
  assume bnj605.37: |- ( ( n =/= 1o /\ n e. D ) -> E. m E. p et )
  assume bnj605.38: |- ( ( th /\ m e. D /\ m _E n ) -> ch' )
  assume bnj605.41: |- ( ( R _FrSe A /\ ta /\ et ) -> f Fn n )
  assume bnj605.42: |- ( ( R _FrSe A /\ ta /\ et ) -> ph" )
  assume bnj605.43: |- ( ( R _FrSe A /\ ta /\ et ) -> ps" )

  disjoint A f
  disjoint A m
  disjoint f m
  disjoint A p
  disjoint f p
  disjoint R f
  disjoint R m
  disjoint R p
  disjoint et f
  disjoint m n
  disjoint m ph
  disjoint m ps
  disjoint m x
  disjoint n p
  disjoint p ph
  disjoint p ps
  disjoint p th
  disjoint p x
  assert |- ( ( n =/= 1o /\ n e. D /\ th ) -> ( ( R _FrSe A /\ x e. A ) -> E. f ( f Fn n /\ ph /\ ps ) ) )

  proof
    vn
    cv
    #
    c1o
    wne
    #
    @0
    cD
    wcel
    #
    wth
    cA
    cR
    w-bnj15
    #
    vx
    cv
    cA
    wcel
    #
    wa
    #
    vf
    cv
    #
    @0
    wfn
    #
    wph
    wps
    w3a
    #
    vf
    wex
    #
    wi
    #
    @1
    @2
    wa
    #
    wth
    wa
    #
    wet
    wth
    wa
    #
    vp
    wex
    #
    vm
    wex
    #
    bnjwchm
    wet
    wa
    #
    vp
    wex
    vm
    wex
    @10
    @12
    wet
    vp
    wex
    #
    vm
    wex
    #
    wth
    wa
    #
    @15
    @11
    @18
    wth
    bnj605.37
    anim1i
    @15
    @17
    wth
    wa
    #
    vm
    wex
    @19
    @14
    @20
    vm
    wet
    wth
    vp
    wth
    vp
    nfv
    19.41
    exbii
    @17
    wth
    vm
    wth
    vm
    wth
    vm
    cv
    #
    @0
    cep
    wbr
    #
    wch
    vn
    @21
    wsbc
    wi
    vm
    cD
    bnj605.5
    bnj1095
    nf5i
    19.41
    bitr2i
    sylib
    @13
    @16
    vm
    vp
    @13
    bnjwchm
    wet
    @13
    wth
    @21
    cD
    wcel
    #
    @22
    w3a
    #
    bnjwchm
    @13
    @23
    @22
    wa
    #
    wth
    wa
    @24
    wet
    @25
    wth
    wet
    @23
    @22
    wet
    @23
    @0
    @21
    csuc
    wceq
    #
    vp
    cv
    #
    com
    wcel
    #
    @21
    @27
    csuc
    wceq
    #
    bnj605.19
    bnj1232
    @23
    @26
    @28
    @29
    @22
    wet
    bnj605.19
    vm
    vn
    bnj219
    bnj770
    jca
    anim1i
    wth
    @23
    @22
    bnj170
    sylibr
    bnj605.38
    syl
    wet
    wth
    simpl
    jca
    2eximi
    @16
    @10
    vm
    vp
    @16
    @5
    @9
    @3
    @4
    bnjwchm
    wet
    w-bnj17
    #
    @7
    bnjwphn
    bnjwpsn
    w3a
    #
    vf
    wex
    #
    @16
    @5
    wa
    @9
    @30
    wta
    vf
    wex
    #
    @32
    @5
    bnjwchm
    wa
    #
    wet
    @33
    @30
    @3
    @4
    bnjwchm
    wet
    bnj248
    #
    @34
    @6
    @21
    wfn
    bnjwphm
    bnjwpsm
    w3a
    #
    vf
    wta
    @34
    @36
    vf
    weu
    #
    @36
    vf
    wex
    bnjwchm
    @5
    @5
    @37
    wi
    @37
    bnj605.31
    @5
    @37
    pm3.35
    sylan2b
    @36
    vf
    euex
    syl
    bnj605.17
    bnj1198
    bnj832
    @30
    @34
    wet
    wa
    @33
    @32
    wi
    #
    @35
    @5
    wet
    @38
    bnjwchm
    @3
    wet
    @38
    @4
    @3
    wet
    wa
    wta
    @31
    vf
    @3
    wet
    wta
    @31
    @3
    wta
    wet
    @31
    @3
    wta
    wet
    w3a
    @7
    bnjwphn
    bnjwpsn
    bnj605.41
    bnj605.42
    bnj605.43
    3jca
    3com23
    3expia
    eximdv
    adantlr
    adantlr
    sylbi
    mpd
    @3
    @4
    bnjwchm
    wet
    bnj432
    @31
    @8
    vf
    @7
    @7
    bnjwphn
    wph
    bnjwpsn
    wps
    @7
    biid
    bnjwphn
    wph
    vf
    @6
    wsbc
    wph
    bnj605.13
    wph
    vf
    sbcid
    bitri
    bnjwpsn
    wps
    vf
    @6
    wsbc
    wps
    bnj605.14
    wps
    vf
    sbcid
    bitri
    3anbi123i
    exbii
    3imtr3i
    ex
    exlimivv
    3syl
    3impa
end
