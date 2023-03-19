include "cv.mm"
include "c1o.mm"
include "wne.mm"
include "wcel.mm"
include "w3a.mm"
include "w-bnj15.mm"
include "wa.mm"
include "wfn.mm"
include "weu.mm"
include "wi.mm"
include "wex.mm"
include "wmo.mm"
include "wsbc.mm"
include "bnj528.mm"
include "vex.mm"
include "bnj207.mm"
include "bnj609.mm"
include "bnj611.mm"
include "csuc.mm"
include "wceq.mm"
include "com.mm"
include "w-bnj17.mm"
include "wrex.mm"
include "bnj168.mm"
include "df-rex.mm"
include "sylib.mm"
include "bnj158.mm"
include "adantr.mm"
include "ancri.mm"
include "bnj534.mm"
include "bnj432.mm"
include "exbii.mm"
include "sylibr.mm"
include "eximi.mm"
include "syl.mm"
include "2exbii.mm"
include "cep.mm"
include "wbr.mm"
include "wral.mm"
include "rsp.mm"
include "sylbi.mm"
include "3imp.mm"
include "bnj523.mm"
include "bnj539.mm"
include "bnj544.mm"
include "bnj561.mm"
include "bnj545.mm"
include "bnj562.mm"
include "bnj571.mm"
include "biid.mm"
include "bnj607.mm"
include "bnj579.mm"
include "a1d.mm"
include "3ad2ant2.mm"
include "jcad.mm"
include "eu5.mm"
include "syl6ibr.mm"
include "3expib.mm"

theorem bnj600
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let wth: wff th
  let wta: wff ta
  let wet: wff et
  let wze: wff ze
  let wsi: wff si
  let wrh: wff rh
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cR: class R
  let vf: setvar f
  let vi: setvar i
  let vm: setvar m
  let vn: setvar n
  let cG: class G
  let cK: class K
  let cL: class L
  let vp: setvar p
  let bnjwphm: wff ph'
  let bnjwpsm: wff ps'
  let bnjwchm: wff ch'
  let bnjwphn: wff ph"
  let bnjwpsn: wff ps"
  let bnjwchn: wff ch"
  let vz: setvar z
  assume bnj600.1: |- ( ph <-> ( f ` (/) ) = _pred ( x , A , R ) )
  assume bnj600.2: |- ( ps <-> A. i e. _om ( suc i e. n -> ( f ` suc i ) = U_ y e. ( f ` i ) _pred ( y , A , R ) ) )
  assume bnj600.3: |- D = ( _om \ { (/) } )
  assume bnj600.4: |- ( ch <-> ( ( R _FrSe A /\ x e. A ) -> E! f ( f Fn n /\ ph /\ ps ) ) )
  assume bnj600.5: |- ( th <-> A. m e. D ( m _E n -> [. m / n ]. ch ) )
  assume bnj600.10: |- ( ph' <-> [. m / n ]. ph )
  assume bnj600.11: |- ( ps' <-> [. m / n ]. ps )
  assume bnj600.12: |- ( ch' <-> [. m / n ]. ch )
  assume bnj600.13: |- ( ph" <-> [. G / f ]. ph )
  assume bnj600.14: |- ( ps" <-> [. G / f ]. ps )
  assume bnj600.15: |- ( ch" <-> [. G / f ]. ch )
  assume bnj600.16: |- G = ( f u. { <. m , U_ y e. ( f ` p ) _pred ( y , A , R ) >. } )
  assume bnj600.17: |- ( ta <-> ( f Fn m /\ ph' /\ ps' ) )
  assume bnj600.18: |- ( si <-> ( m e. D /\ n = suc m /\ p e. m ) )
  assume bnj600.19: |- ( et <-> ( m e. D /\ n = suc m /\ p e. _om /\ m = suc p ) )
  assume bnj600.20: |- ( ze <-> ( i e. _om /\ suc i e. n /\ m = suc i ) )
  assume bnj600.21: |- ( rh <-> ( i e. _om /\ suc i e. n /\ m =/= suc i ) )
  assume bnj600.22: |- B = U_ y e. ( f ` i ) _pred ( y , A , R )
  assume bnj600.23: |- C = U_ y e. ( f ` p ) _pred ( y , A , R )
  assume bnj600.24: |- K = U_ y e. ( G ` i ) _pred ( y , A , R )
  assume bnj600.25: |- L = U_ y e. ( G ` p ) _pred ( y , A , R )
  assume bnj600.26: |- G = ( f u. { <. m , C >. } )

  disjoint A f
  disjoint A i
  disjoint A m
  disjoint A n
  disjoint A p
  disjoint f i
  disjoint f m
  disjoint f n
  disjoint f p
  disjoint i m
  disjoint i n
  disjoint i p
  disjoint m n
  disjoint m p
  disjoint n p
  disjoint A y
  disjoint f y
  disjoint i y
  disjoint n y
  disjoint p y
  disjoint D f
  disjoint D p
  disjoint G i
  disjoint G y
  disjoint R f
  disjoint R i
  disjoint R m
  disjoint R n
  disjoint R p
  disjoint R y
  disjoint et f
  disjoint et i
  disjoint f x
  disjoint m x
  disjoint n x
  disjoint p x
  disjoint i ph'
  disjoint p ph'
  disjoint m ph
  disjoint p ph
  disjoint m ps
  disjoint p ps
  disjoint p th
  disjoint A z
  disjoint f z
  disjoint i z
  disjoint m z
  disjoint n z
  disjoint p z
  disjoint G z
  disjoint y z
  disjoint R z
  disjoint x z
  disjoint ph z
  disjoint ps z
  assert |- ( n =/= 1o -> ( ( n e. D /\ th ) -> ch ) )

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
    wch
    @1
    @2
    wth
    w3a
    #
    cA
    cR
    w-bnj15
    vx
    cv
    #
    cA
    wcel
    wa
    #
    vf
    cv
    #
    @0
    wfn
    wph
    wps
    w3a
    #
    vf
    weu
    #
    wi
    wch
    @3
    @5
    @7
    vf
    wex
    #
    @7
    vf
    wmo
    #
    wa
    @8
    @3
    @5
    @9
    @10
    wph
    wps
    wch
    wth
    wta
    wet
    vx
    vy
    cA
    cD
    cR
    vf
    vz
    vi
    vm
    vn
    cG
    vp
    bnjwphm
    bnjwpsm
    bnjwchm
    bnjwphn
    bnjwpsn
    wph
    vf
    vz
    cv
    #
    wsbc
    #
    wps
    vf
    @11
    wsbc
    #
    @12
    vz
    cG
    wsbc
    #
    @13
    vz
    cG
    wsbc
    #
    bnj600.5
    bnj600.13
    bnj600.14
    bnj600.17
    bnj600.19
    vy
    cA
    cR
    vf
    vm
    cG
    vp
    bnj600.16
    bnj528
    #
    wph
    wps
    wch
    vx
    cA
    cR
    vf
    vn
    vm
    cv
    #
    bnjwphm
    bnjwpsm
    bnjwchm
    bnj600.4
    bnj600.10
    bnj600.11
    bnj600.12
    vm
    vex
    #
    bnj207
    wph
    cA
    cR
    vf
    cG
    @4
    bnjwphn
    bnj600.1
    bnj600.13
    @16
    bnj609
    #
    wps
    vy
    cA
    cR
    vf
    vi
    cG
    @0
    bnjwpsn
    bnj600.2
    bnj600.14
    @16
    bnj611
    #
    @1
    @2
    wa
    #
    @17
    cD
    wcel
    #
    @0
    @17
    csuc
    wceq
    #
    vp
    cv
    #
    com
    wcel
    #
    @17
    @24
    csuc
    wceq
    #
    w-bnj17
    #
    vp
    wex
    #
    vm
    wex
    #
    wet
    vp
    wex
    vm
    wex
    @21
    @22
    @23
    wa
    #
    vm
    wex
    #
    @29
    @21
    @23
    vm
    cD
    wrex
    @31
    cD
    vm
    vn
    bnj600.3
    bnj168
    @23
    vm
    cD
    df-rex
    sylib
    @30
    @28
    vm
    @30
    @25
    @26
    wa
    #
    @30
    wa
    #
    vp
    wex
    @28
    @32
    @30
    @30
    vp
    @30
    @32
    vp
    wex
    #
    @22
    @34
    @23
    @22
    @26
    vp
    com
    wrex
    @34
    cD
    vm
    vp
    bnj600.3
    bnj158
    @26
    vp
    com
    df-rex
    sylib
    adantr
    ancri
    bnj534
    @27
    @33
    vp
    @22
    @23
    @25
    @26
    bnj432
    exbii
    sylibr
    eximi
    syl
    wet
    @27
    vm
    vp
    bnj600.19
    2exbii
    sylibr
    wth
    @22
    @17
    @0
    cep
    wbr
    #
    w3a
    wch
    vn
    @17
    wsbc
    #
    bnjwchm
    wth
    @22
    @35
    @36
    wth
    @35
    @36
    wi
    #
    vm
    cD
    wral
    @22
    @37
    wi
    bnj600.5
    @37
    vm
    cD
    rsp
    sylbi
    3imp
    bnj600.12
    sylibr
    wta
    wet
    wsi
    cA
    cD
    cR
    vm
    vn
    cG
    vp
    bnj600.18
    bnj600.19
    wta
    wsi
    vx
    vy
    cA
    cD
    cR
    vf
    vi
    vm
    vn
    cG
    vp
    bnjwphm
    bnjwpsm
    wph
    cA
    cR
    vn
    @6
    @17
    @4
    bnjwphm
    bnj600.1
    bnj600.10
    @18
    bnj523
    #
    wps
    vy
    cA
    cR
    vi
    vn
    @6
    @17
    bnjwpsm
    bnj600.2
    bnj600.11
    @18
    bnj539
    #
    bnj600.3
    bnj600.16
    bnj600.17
    bnj600.18
    bnj544
    #
    bnj561
    #
    wta
    wet
    wsi
    cA
    cD
    cR
    vm
    vn
    vp
    bnjwphn
    bnj600.18
    bnj600.19
    wta
    wsi
    vx
    vy
    cA
    cD
    cR
    vf
    vm
    vn
    cG
    vp
    bnjwphm
    bnjwpsm
    bnjwphn
    @38
    bnj600.3
    bnj600.16
    bnj600.17
    bnj600.18
    @40
    @19
    bnj545
    bnj562
    wta
    wet
    wze
    wsi
    wrh
    vx
    vy
    cA
    cB
    cC
    cD
    cR
    vf
    vi
    vm
    vn
    cG
    cK
    cL
    vp
    bnjwphm
    bnjwpsm
    bnjwpsn
    bnj600.3
    bnj600.16
    bnj600.17
    bnj600.18
    bnj600.19
    bnj600.20
    bnj600.22
    bnj600.23
    bnj600.24
    bnj600.25
    bnj600.26
    @38
    @39
    @40
    bnj600.21
    @41
    @20
    bnj571
    bnj600.1
    bnj600.2
    @12
    biid
    @13
    biid
    @14
    biid
    @15
    biid
    bnj607
    @2
    @1
    @5
    @10
    wi
    wth
    @2
    @10
    @5
    wph
    wps
    vx
    vy
    cA
    cD
    cR
    vf
    vi
    vn
    bnj600.1
    bnj600.2
    bnj600.3
    bnj579
    a1d
    3ad2ant2
    jcad
    @7
    vf
    eu5
    syl6ibr
    bnj600.4
    sylibr
    3expib
end
