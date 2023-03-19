include "com.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "csuc.mm"
include "cdif.mm"
include "c0.mm"
include "cv.mm"
include "cmpt.mm"
include "ccom.mm"
include "fveq1i.mm"
include "wf.mm"
include "wceq.mm"
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
include "adantr.mm"
include "ffvelrn.mm"
include "sylancom.mm"
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
include "wne.mm"
include "psseq12d.mm"
include "elrab2.mm"
include "simprbi.mm"
include "df-pss.mm"
include "sylib.mm"
include "pssdifn0.mm"
include "eqnetrd.mm"

theorem isf32lem6
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let cA: class A
  let cS: class S
  let cF: class F
  let cG: class G
  let cJ: class J
  let cK: class K
  let va: setvar a
  let vb: setvar b
  let cB: class B
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
  disjoint B w
  disjoint B x
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
  assert |- ( ( ph /\ A e. _om ) -> ( K ` A ) =/= (/) )

  proof
    wph
    cA
    com
    wcel
    #
    wa
    #
    cA
    cK
    cfv
    #
    cA
    cJ
    cfv
    #
    cF
    cfv
    #
    @3
    csuc
    #
    cF
    cfv
    #
    cdif
    #
    c0
    @1
    @2
    cA
    vw
    cS
    vw
    cv
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
    cmpt
    #
    cJ
    ccom
    #
    cfv
    #
    @7
    cA
    cK
    @14
    isf32lem.f
    fveq1i
    @1
    @15
    @3
    @13
    cfv
    #
    @7
    wph
    com
    cS
    cJ
    wf
    #
    @0
    @15
    @16
    wceq
    wph
    com
    cS
    cJ
    wf1o
    #
    @17
    wph
    cS
    com
    wss
    #
    cS
    cfn
    wcel
    wn
    #
    @18
    cS
    vy
    cv
    #
    csuc
    #
    cF
    cfv
    #
    @21
    cF
    cfv
    #
    wpss
    #
    vy
    com
    crab
    com
    isf32lem.d
    @25
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
    #
    cJ
    cS
    vu
    vv
    isf32lem.e
    fin23lem22
    #
    sylancr
    com
    cS
    cJ
    f1of
    #
    syl
    com
    cS
    cA
    @13
    cJ
    fvco3
    sylan
    @1
    @3
    cS
    wcel
    #
    @16
    @7
    wceq
    wph
    @0
    @17
    @30
    @1
    @18
    @17
    @1
    @19
    @20
    @18
    @26
    wph
    @20
    @0
    @27
    adantr
    @28
    sylancr
    @29
    syl
    com
    cS
    cA
    cJ
    ffvelrn
    sylancom
    #
    vw
    @3
    @12
    @7
    cS
    @13
    @8
    @3
    wceq
    #
    @9
    @4
    @11
    @6
    @8
    @3
    cF
    fveq2
    @32
    @10
    @5
    cF
    @8
    @3
    suceq
    fveq2d
    difeq12d
    @13
    eqid
    @4
    cvv
    wcel
    @7
    cvv
    wcel
    @3
    cF
    fvex
    @4
    @6
    cvv
    difexg
    ax-mp
    fvmpt
    syl
    eqtrd
    syl5eq
    @1
    @6
    @4
    wss
    @6
    @4
    wne
    wa
    #
    @7
    c0
    wne
    @1
    @6
    @4
    wpss
    #
    @33
    @1
    @30
    @34
    @31
    @30
    @3
    com
    wcel
    @34
    @25
    @34
    vy
    @3
    com
    cS
    @21
    @3
    wceq
    #
    @23
    @6
    @24
    @4
    @35
    @22
    @5
    cF
    @21
    @3
    suceq
    fveq2d
    @21
    @3
    cF
    fveq2
    psseq12d
    isf32lem.d
    elrab2
    simprbi
    syl
    @6
    @4
    df-pss
    sylib
    @6
    @4
    pssdifn0
    syl
    eqnetrd
end
