include "wne.mm"
include "wa.mm"
include "com.mm"
include "wcel.mm"
include "cfv.mm"
include "cin.mm"
include "csuc.mm"
include "cdif.mm"
include "c0.mm"
include "cv.mm"
include "cmpt.mm"
include "ccom.mm"
include "fveq1i.mm"
include "wceq.mm"
include "wf.mm"
include "wf1o.mm"
include "wss.mm"
include "cfn.mm"
include "wn.mm"
include "wpss.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "isf32lem5.mm"
include "fin23lem22.mm"
include "sylancr.mm"
include "f1of.mm"
include "syl.mm"
include "fvco3.mm"
include "sylan.mm"
include "ad2ant2r.mm"
include "adantr.mm"
include "simpl.mm"
include "ffvelrn.mm"
include "syl2an.mm"
include "fveq2.mm"
include "suceq.mm"
include "fveq2d.mm"
include "difeq12d.mm"
include "eqid.mm"
include "cvv.mm"
include "fvex.mm"
include "difexg.mm"
include "ax-mp.mm"
include "fvmpt.mm"
include "eqtrd.mm"
include "syl5eq.mm"
include "ad2ant2rl.mm"
include "simpr.mm"
include "ineq12d.mm"
include "simpll.mm"
include "simplr.mm"
include "wf1.mm"
include "wb.mm"
include "f1of1.mm"
include "f1fveq.mm"
include "biimpd.mm"
include "necon3d.mm"
include "mpd.mm"
include "sseldi.mm"
include "isf32lem4.mm"
include "syl22anc.mm"

theorem isf32lem7
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let cB: class B
  let cS: class S
  let cF: class F
  let cG: class G
  let cJ: class J
  let cK: class K
  let va: setvar a
  let vb: setvar b
  let vt: setvar t
  let cL: class L
  let vc: setvar c
  let vs: setvar s
  let vd: setvar d
  assume isf32lem.a: |- ( ph -> F : _om --> ~P G )
  assume isf32lem.b: |- ( ph -> A. x e. _om ( F ` suc x ) C_ ( F ` x ) )
  assume isf32lem.c: |- ( ph -> -. |^| ran F e. ran F )
  assume isf32lem.d: |- S = { y e. _om | ( F ` suc y ) C. ( F ` y ) }
  assume isf32lem.e: |- J = ( u e. _om |-> ( iota_ v e. S ( v i^i S ) ~~ u ) )
  assume isf32lem.f: |- K = ( ( w e. S |-> ( ( F ` w ) \ ( F ` suc w ) ) ) o. J )

  disjoint w x
  disjoint B w
  disjoint B x
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
  disjoint A w
  disjoint A x
  disjoint A y
  disjoint F w
  disjoint F x
  disjoint F y
  disjoint S u
  disjoint S v
  disjoint S w
  disjoint S x
  disjoint S y
  disjoint J w
  disjoint J x
  disjoint J y
  disjoint K x
  disjoint K y
  disjoint a b
  disjoint a w
  disjoint a x
  disjoint B a
  disjoint b w
  disjoint b x
  disjoint B b
  disjoint a t
  disjoint G a
  disjoint b t
  disjoint G b
  disjoint G t
  disjoint L a
  disjoint L b
  disjoint L x
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
  disjoint F a
  disjoint F b
  disjoint F c
  disjoint F d
  disjoint S a
  disjoint S b
  disjoint S s
  disjoint S t
  disjoint J s
  disjoint J t
  disjoint K a
  disjoint K b
  disjoint K s
  disjoint K t
  assert |- ( ( ( ph /\ A =/= B ) /\ ( A e. _om /\ B e. _om ) ) -> ( ( K ` A ) i^i ( K ` B ) ) = (/) )

  proof
    wph
    cA
    cB
    wne
    #
    wa
    #
    cA
    com
    wcel
    #
    cB
    com
    wcel
    #
    wa
    #
    wa
    #
    cA
    cK
    cfv
    #
    cB
    cK
    cfv
    #
    cin
    cA
    cJ
    cfv
    #
    cF
    cfv
    #
    @8
    csuc
    #
    cF
    cfv
    #
    cdif
    #
    cB
    cJ
    cfv
    #
    cF
    cfv
    #
    @13
    csuc
    #
    cF
    cfv
    #
    cdif
    #
    cin
    #
    c0
    @5
    @6
    @12
    @7
    @17
    @5
    @6
    cA
    vw
    cS
    vw
    cv
    #
    cF
    cfv
    #
    @19
    csuc
    #
    cF
    cfv
    #
    cdif
    #
    cmpt
    #
    cJ
    ccom
    #
    cfv
    #
    @12
    cA
    cK
    @25
    isf32lem.f
    fveq1i
    @5
    @26
    @8
    @24
    cfv
    #
    @12
    wph
    @2
    @26
    @27
    wceq
    #
    @0
    @3
    wph
    com
    cS
    cJ
    wf
    #
    @2
    @28
    wph
    com
    cS
    cJ
    wf1o
    #
    @29
    wph
    cS
    com
    wss
    cS
    cfn
    wcel
    wn
    @30
    cS
    vy
    cv
    #
    csuc
    cF
    cfv
    @31
    cF
    cfv
    wpss
    #
    vy
    com
    crab
    com
    isf32lem.d
    @32
    vy
    com
    ssrab2
    eqsstri
    #
    wph
    vx
    vy
    cS
    cF
    cG
    isf32lem.a
    isf32lem.b
    isf32lem.c
    isf32lem.d
    isf32lem5
    cJ
    cS
    vu
    vv
    isf32lem.e
    fin23lem22
    sylancr
    #
    com
    cS
    cJ
    f1of
    syl
    #
    com
    cS
    cA
    @24
    cJ
    fvco3
    sylan
    ad2ant2r
    @5
    @8
    cS
    wcel
    #
    @27
    @12
    wceq
    @1
    @29
    @2
    @36
    @4
    wph
    @29
    @0
    @35
    adantr
    #
    @2
    @3
    simpl
    com
    cS
    cA
    cJ
    ffvelrn
    syl2an
    #
    vw
    @8
    @23
    @12
    cS
    @24
    @19
    @8
    wceq
    #
    @20
    @9
    @22
    @11
    @19
    @8
    cF
    fveq2
    @39
    @21
    @10
    cF
    @19
    @8
    suceq
    fveq2d
    difeq12d
    @24
    eqid
    #
    @9
    cvv
    wcel
    @12
    cvv
    wcel
    @8
    cF
    fvex
    @9
    @11
    cvv
    difexg
    ax-mp
    fvmpt
    syl
    eqtrd
    syl5eq
    @5
    @7
    cB
    @25
    cfv
    #
    @17
    cB
    cK
    @25
    isf32lem.f
    fveq1i
    @5
    @41
    @13
    @24
    cfv
    #
    @17
    wph
    @3
    @41
    @42
    wceq
    #
    @0
    @2
    wph
    @29
    @3
    @43
    @35
    com
    cS
    cB
    @24
    cJ
    fvco3
    sylan
    ad2ant2rl
    @5
    @13
    cS
    wcel
    #
    @42
    @17
    wceq
    @1
    @29
    @3
    @44
    @4
    @37
    @2
    @3
    simpr
    com
    cS
    cB
    cJ
    ffvelrn
    syl2an
    #
    vw
    @13
    @23
    @17
    cS
    @24
    @19
    @13
    wceq
    #
    @20
    @14
    @22
    @16
    @19
    @13
    cF
    fveq2
    @46
    @21
    @15
    cF
    @19
    @13
    suceq
    fveq2d
    difeq12d
    @40
    @14
    cvv
    wcel
    @17
    cvv
    wcel
    @13
    cF
    fvex
    @14
    @16
    cvv
    difexg
    ax-mp
    fvmpt
    syl
    eqtrd
    syl5eq
    ineq12d
    @5
    wph
    @8
    @13
    wne
    #
    @8
    com
    wcel
    @13
    com
    wcel
    @18
    c0
    wceq
    wph
    @0
    @4
    simpll
    @5
    @0
    @47
    wph
    @0
    @4
    simplr
    @5
    @8
    @13
    cA
    cB
    @5
    @8
    @13
    wceq
    #
    cA
    cB
    wceq
    #
    @1
    com
    cS
    cJ
    wf1
    #
    @4
    @48
    @49
    wb
    wph
    @50
    @0
    wph
    @30
    @50
    @34
    com
    cS
    cJ
    f1of1
    syl
    adantr
    com
    cS
    cA
    cB
    cJ
    f1fveq
    sylan
    biimpd
    necon3d
    mpd
    @5
    cS
    com
    @8
    @33
    @38
    sseldi
    @5
    cS
    com
    @13
    @33
    @45
    sseldi
    wph
    vx
    @8
    @13
    cF
    cG
    isf32lem.a
    isf32lem.b
    isf32lem.c
    isf32lem4
    syl22anc
    eqtrd
end
