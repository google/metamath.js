include "com.mm"
include "wfo.mm"
include "wcel.mm"
include "cvv.mm"
include "cwdom.mm"
include "wbr.mm"
include "isf32lem9.mm"
include "wf.mm"
include "fof.mm"
include "syl.mm"
include "fex.mm"
include "sylan.mm"
include "ex.mm"
include "fowdom.mm"
include "expcom.mm"
include "sylsyld.mm"

theorem isf32lem10
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
  let cV: class V
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
  assert |- ( ph -> ( G e. V -> _om ~<_* G ) )

  proof
    wph
    cG
    com
    cL
    wfo
    #
    cG
    cV
    wcel
    #
    cL
    cvv
    wcel
    #
    com
    cG
    cwdom
    wbr
    #
    wph
    vx
    vy
    vw
    vv
    vu
    vt
    cS
    cF
    cG
    cJ
    cK
    cL
    vs
    isf32lem.a
    isf32lem.b
    isf32lem.c
    isf32lem.d
    isf32lem.e
    isf32lem.f
    isf32lem.g
    isf32lem9
    #
    wph
    @1
    @2
    wph
    cG
    com
    cL
    wf
    #
    @1
    @2
    wph
    @0
    @5
    @4
    cG
    com
    cL
    fof
    syl
    cG
    com
    cV
    cL
    fex
    sylan
    ex
    @2
    @0
    @3
    cL
    cvv
    com
    cG
    fowdom
    expcom
    sylsyld
end
