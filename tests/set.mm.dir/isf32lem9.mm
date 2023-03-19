include "com.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wrex.mm"
include "wral.mm"
include "wfo.mm"
include "wcel.mm"
include "wa.mm"
include "cio.mm"
include "weu.mm"
include "cab.mm"
include "ssab2.mm"
include "iotacl.mm"
include "sseldi.mm"
include "wn.mm"
include "c0.mm"
include "iotanul.mm"
include "peano1.mm"
include "syl6eqel.mm"
include "pm2.61i.mm"
include "a1i.mm"
include "fmpti.mm"
include "wex.mm"
include "wne.mm"
include "isf32lem6.mm"
include "n0.mm"
include "sylib.mm"
include "isf32lem8.mm"
include "sselda.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "iotabidv.mm"
include "iotaex.mm"
include "fvmpt3i.mm"
include "syl.mm"
include "wi.mm"
include "w3a.mm"
include "simp1r.mm"
include "wal.mm"
include "cin.mm"
include "simpl1.mm"
include "simpr.mm"
include "necomd.mm"
include "simpl2.mm"
include "simpl3.mm"
include "isf32lem7.mm"
include "syl22anc.mm"
include "disj1.mm"
include "ex.mm"
include "sp.mm"
include "syl6.mm"
include "com23.mm"
include "3adant1r.mm"
include "mpd.mm"
include "necon4ad.mm"
include "3expia.mm"
include "impd.mm"
include "fveq2.mm"
include "eleq2d.mm"
include "anbi12d.mm"
include "biimprcd.mm"
include "ancoms.mm"
include "adantll.mm"
include "impbid.mm"
include "iota5.mm"
include "an32s.mm"
include "eqtr2d.mm"
include "jca.mm"
include "eximdv.mm"
include "df-rex.mm"
include "syl6ibr.mm"
include "ralrimiva.mm"
include "dffo3.mm"
include "sylanbrc.mm"

theorem isf32lem9
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let vt: setvar t
  let cS: class S
  let cF: class F
  let cG: class G
  let cJ: class J
  let cK: class K
  let cL: class L
  let vs: setvar s
  let va: setvar a
  let vb: setvar b
  let cB: class B
  let vc: setvar c
  let vd: setvar d
  let cA: class A
  assume isf32lem.a: |- ( ph -> F : _om --> ~P G )
  assume isf32lem.b: |- ( ph -> A. x e. _om ( F ` suc x ) C_ ( F ` x ) )
  assume isf32lem.c: |- ( ph -> -. |^| ran F e. ran F )
  assume isf32lem.d: |- S = { y e. _om | ( F ` suc y ) C. ( F ` y ) }
  assume isf32lem.e: |- J = ( u e. _om |-> ( iota_ v e. S ( v i^i S ) ~~ u ) )
  assume isf32lem.f: |- K = ( ( w e. S |-> ( ( F ` w ) \ ( F ` suc w ) ) ) o. J )
  assume isf32lem.g: |- L = ( t e. G |-> ( iota s ( s e. _om /\ t e. ( K ` s ) ) ) )

  disjoint w x
  disjoint G t
  disjoint L x
  disjoint s t
  disjoint s u
  disjoint s v
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint ph s
  disjoint t u
  disjoint t v
  disjoint t w
  disjoint t x
  disjoint t y
  disjoint ph t
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint ph u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint ph v
  disjoint w y
  disjoint ph w
  disjoint x y
  disjoint ph x
  disjoint ph y
  disjoint F w
  disjoint F x
  disjoint F y
  disjoint S s
  disjoint S t
  disjoint S u
  disjoint S v
  disjoint S w
  disjoint S x
  disjoint S y
  disjoint J s
  disjoint J t
  disjoint J w
  disjoint J x
  disjoint J y
  disjoint K s
  disjoint K t
  disjoint K x
  disjoint K y
  disjoint a b
  disjoint a w
  disjoint a x
  disjoint B a
  disjoint b w
  disjoint b x
  disjoint B b
  disjoint B w
  disjoint B x
  disjoint a t
  disjoint G a
  disjoint b t
  disjoint G b
  disjoint L a
  disjoint L b
  disjoint a c
  disjoint a s
  disjoint a u
  disjoint a v
  disjoint a y
  disjoint a ph
  disjoint b c
  disjoint b s
  disjoint b u
  disjoint b v
  disjoint b y
  disjoint b ph
  disjoint c s
  disjoint c t
  disjoint c u
  disjoint c v
  disjoint c w
  disjoint c x
  disjoint c y
  disjoint c ph
  disjoint a d
  disjoint A a
  disjoint b d
  disjoint A b
  disjoint c d
  disjoint A c
  disjoint d w
  disjoint d x
  disjoint d y
  disjoint A d
  disjoint A w
  disjoint A x
  disjoint A y
  disjoint F a
  disjoint F b
  disjoint F c
  disjoint F d
  disjoint S a
  disjoint S b
  disjoint K a
  disjoint K b
  assert |- ( ph -> L : G -onto-> _om )

  proof
    wph
    cG
    com
    cL
    wf
    #
    va
    cv
    #
    vb
    cv
    #
    cL
    cfv
    #
    wceq
    #
    vb
    cG
    wrex
    #
    va
    com
    wral
    cG
    com
    cL
    wfo
    @0
    wph
    vt
    cG
    com
    vs
    cv
    #
    com
    wcel
    #
    vt
    cv
    #
    @6
    cK
    cfv
    #
    wcel
    #
    wa
    #
    vs
    cio
    #
    cL
    isf32lem.g
    @12
    com
    wcel
    #
    @8
    cG
    wcel
    @11
    vs
    weu
    #
    @13
    @14
    @11
    vs
    cab
    com
    @12
    @10
    vs
    com
    ssab2
    @11
    vs
    iotacl
    sseldi
    @14
    wn
    @12
    c0
    com
    @11
    vs
    iotanul
    peano1
    syl6eqel
    pm2.61i
    a1i
    fmpti
    a1i
    wph
    @5
    va
    com
    wph
    @1
    com
    wcel
    #
    wa
    #
    @2
    @1
    cK
    cfv
    #
    wcel
    #
    vb
    wex
    #
    @5
    @16
    @17
    c0
    wne
    @19
    wph
    vx
    vy
    vw
    vv
    vu
    @1
    cS
    cF
    cG
    cJ
    cK
    isf32lem.a
    isf32lem.b
    isf32lem.c
    isf32lem.d
    isf32lem.e
    isf32lem.f
    isf32lem6
    vb
    @17
    n0
    sylib
    @16
    @19
    @2
    cG
    wcel
    #
    @4
    wa
    #
    vb
    wex
    @5
    @16
    @18
    @21
    vb
    @16
    @18
    @21
    @16
    @18
    wa
    #
    @20
    @4
    @16
    @17
    cG
    @2
    wph
    vx
    vy
    vw
    vv
    vu
    @1
    cS
    cF
    cG
    cJ
    cK
    isf32lem.a
    isf32lem.b
    isf32lem.c
    isf32lem.d
    isf32lem.e
    isf32lem.f
    isf32lem8
    sselda
    #
    @22
    @3
    @7
    @2
    @9
    wcel
    #
    wa
    #
    vs
    cio
    #
    @1
    @22
    @20
    @3
    @26
    wceq
    @23
    vt
    @2
    @12
    @26
    cG
    cL
    @8
    @2
    wceq
    #
    @11
    @25
    vs
    @27
    @10
    @24
    @7
    @8
    @2
    @9
    eleq1
    anbi2d
    iotabidv
    isf32lem.g
    @11
    vs
    iotaex
    fvmpt3i
    syl
    wph
    @18
    @15
    @26
    @1
    wceq
    wph
    @18
    wa
    #
    @25
    vs
    @1
    com
    @28
    @15
    wa
    #
    @25
    @6
    @1
    wceq
    #
    @29
    @7
    @24
    @30
    @28
    @15
    @7
    @24
    @30
    wi
    @28
    @15
    @7
    w3a
    #
    @24
    @6
    @1
    @31
    @18
    @6
    @1
    wne
    #
    @24
    wn
    #
    wi
    #
    wph
    @18
    @15
    @7
    simp1r
    wph
    @15
    @7
    @18
    @34
    wi
    @18
    wph
    @15
    @7
    w3a
    #
    @32
    @18
    @33
    @35
    @32
    @18
    @33
    wi
    #
    vb
    wal
    #
    @36
    @35
    @32
    @37
    @35
    @32
    wa
    #
    @17
    @9
    cin
    c0
    wceq
    #
    @37
    @38
    wph
    @1
    @6
    wne
    @15
    @7
    @39
    wph
    @15
    @7
    @32
    simpl1
    @38
    @6
    @1
    @35
    @32
    simpr
    necomd
    wph
    @15
    @7
    @32
    simpl2
    wph
    @15
    @7
    @32
    simpl3
    wph
    vx
    vy
    vw
    vv
    vu
    @1
    @6
    cS
    cF
    cG
    cJ
    cK
    isf32lem.a
    isf32lem.b
    isf32lem.c
    isf32lem.d
    isf32lem.e
    isf32lem.f
    isf32lem7
    syl22anc
    vb
    @17
    @9
    disj1
    sylib
    ex
    @36
    vb
    sp
    syl6
    com23
    3adant1r
    mpd
    necon4ad
    3expia
    impd
    @18
    @15
    @30
    @25
    wi
    #
    wph
    @15
    @18
    @40
    @30
    @25
    @15
    @18
    wa
    @30
    @7
    @15
    @24
    @18
    @6
    @1
    com
    eleq1
    @30
    @9
    @17
    @2
    @6
    @1
    cK
    fveq2
    eleq2d
    anbi12d
    biimprcd
    ancoms
    adantll
    impbid
    iota5
    an32s
    eqtr2d
    jca
    ex
    eximdv
    @4
    vb
    cG
    df-rex
    syl6ibr
    mpd
    ralrimiva
    vb
    va
    cG
    com
    cL
    dffo3
    sylanbrc
end
