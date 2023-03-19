include "cfn.mm"
include "wcel.mm"
include "cv.mm"
include "csuc.mm"
include "cfv.mm"
include "wpss.mm"
include "wa.mm"
include "com.mm"
include "wrex.mm"
include "wral.mm"
include "isf32lem2.mm"
include "ralrimiva.mm"
include "wn.mm"
include "cuni.mm"
include "wss.mm"
include "crab.mm"
include "ssrab2.mm"
include "eqsstri.mm"
include "nnunifi.mm"
include "mpan.mm"
include "adantl.mm"
include "wi.mm"
include "elssuni.mm"
include "con0.mm"
include "wb.mm"
include "nnon.mm"
include "omsson.mm"
include "sseldi.mm"
include "ontri1.mm"
include "syl2anr.mm"
include "syl5ib.mm"
include "con2d.mm"
include "impr.mm"
include "eleq2i.mm"
include "sylnib.mm"
include "wceq.mm"
include "suceq.mm"
include "fveq2d.mm"
include "fveq2.mm"
include "psseq12d.mm"
include "elrab3.mm"
include "ad2antrl.mm"
include "mtbid.mm"
include "expr.mm"
include "imnan.mm"
include "sylib.mm"
include "nrexdv.mm"
include "eleq1.mm"
include "anbi1d.mm"
include "rexbidv.mm"
include "notbid.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "rexnal.mm"
include "ex.mm"
include "mt2d.mm"

theorem isf32lem5
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cS: class S
  let cF: class F
  let cG: class G
  let va: setvar a
  let vb: setvar b
  let vw: setvar w
  let cB: class B
  let vt: setvar t
  let cL: class L
  let vc: setvar c
  let vs: setvar s
  let vu: setvar u
  let vv: setvar v
  let vd: setvar d
  let cA: class A
  let cJ: class J
  let cK: class K
  assume isf32lem.a: |- ( ph -> F : _om --> ~P G )
  assume isf32lem.b: |- ( ph -> A. x e. _om ( F ` suc x ) C_ ( F ` x ) )
  assume isf32lem.c: |- ( ph -> -. |^| ran F e. ran F )
  assume isf32lem.d: |- S = { y e. _om | ( F ` suc y ) C. ( F ` y ) }

  disjoint x y
  disjoint ph x
  disjoint ph y
  disjoint F x
  disjoint F y
  disjoint S x
  disjoint S y
  disjoint a b
  disjoint a w
  disjoint a x
  disjoint B a
  disjoint b w
  disjoint b x
  disjoint B b
  disjoint w x
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
  disjoint F w
  disjoint S a
  disjoint S b
  disjoint S s
  disjoint S t
  disjoint S u
  disjoint S v
  disjoint S w
  disjoint J s
  disjoint J t
  disjoint J w
  disjoint J x
  disjoint J y
  disjoint K a
  disjoint K b
  disjoint K s
  disjoint K t
  disjoint K x
  disjoint K y
  assert |- ( ph -> -. S e. Fin )

  proof
    wph
    cS
    cfn
    wcel
    #
    va
    cv
    #
    vb
    cv
    #
    wcel
    #
    @2
    csuc
    #
    cF
    cfv
    #
    @2
    cF
    cfv
    #
    wpss
    #
    wa
    #
    vb
    com
    wrex
    #
    va
    com
    wral
    #
    wph
    @9
    va
    com
    wph
    vx
    @1
    cF
    cG
    vb
    isf32lem.a
    isf32lem.b
    isf32lem.c
    isf32lem2
    ralrimiva
    wph
    @0
    @10
    wn
    #
    wph
    @0
    wa
    #
    @9
    wn
    #
    va
    com
    wrex
    #
    @11
    @12
    cS
    cuni
    #
    com
    wcel
    #
    @15
    @2
    wcel
    #
    @7
    wa
    #
    vb
    com
    wrex
    #
    wn
    #
    @14
    @0
    @16
    wph
    cS
    com
    wss
    @0
    @16
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
    #
    com
    isf32lem.d
    @25
    vy
    com
    ssrab2
    eqsstri
    cS
    nnunifi
    mpan
    adantl
    #
    @12
    @18
    vb
    com
    @12
    @2
    com
    wcel
    #
    wa
    #
    @17
    @7
    wn
    #
    wi
    @18
    wn
    @12
    @28
    @17
    @30
    @12
    @28
    @17
    wa
    wa
    #
    @2
    @26
    wcel
    #
    @7
    @31
    @2
    cS
    wcel
    #
    @32
    @12
    @28
    @17
    @33
    wn
    @29
    @33
    @17
    @33
    @2
    @15
    wss
    #
    @29
    @17
    wn
    #
    @2
    cS
    elssuni
    @28
    @2
    con0
    wcel
    @15
    con0
    wcel
    @34
    @35
    wb
    @12
    @2
    nnon
    @12
    com
    con0
    @15
    omsson
    @27
    sseldi
    @2
    @15
    ontri1
    syl2anr
    syl5ib
    con2d
    impr
    cS
    @26
    @2
    isf32lem.d
    eleq2i
    sylnib
    @28
    @32
    @7
    wb
    @12
    @17
    @25
    @7
    vy
    @2
    com
    @21
    @2
    wceq
    #
    @23
    @5
    @24
    @6
    @36
    @22
    @4
    cF
    @21
    @2
    suceq
    fveq2d
    @21
    @2
    cF
    fveq2
    psseq12d
    elrab3
    ad2antrl
    mtbid
    expr
    @17
    @7
    imnan
    sylib
    nrexdv
    @13
    @20
    va
    @15
    com
    @1
    @15
    wceq
    #
    @9
    @19
    @37
    @8
    @18
    vb
    com
    @37
    @3
    @17
    @7
    @1
    @15
    @2
    eleq1
    anbi1d
    rexbidv
    notbid
    rspcev
    syl2anc
    @9
    va
    com
    rexnal
    sylib
    ex
    mt2d
end
