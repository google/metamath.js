include "wne.mm"
include "wa.mm"
include "com.mm"
include "wcel.mm"
include "cfv.mm"
include "csuc.mm"
include "cdif.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "simplrr.mm"
include "simplrl.mm"
include "simpr.mm"
include "simplll.mm"
include "incom.mm"
include "isf32lem3.mm"
include "syl5eq.mm"
include "syl22anc.mm"
include "wo.mm"
include "simplr.mm"
include "wn.mm"
include "wb.mm"
include "word.mm"
include "nnord.mm"
include "ordtri3.mm"
include "syl2an.mm"
include "adantl.mm"
include "necon2abid.mm"
include "mpbird.mm"
include "mpjaodan.mm"

theorem isf32lem4
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cF: class F
  let cG: class G
  let va: setvar a
  let vb: setvar b
  let vw: setvar w
  let vt: setvar t
  let cL: class L
  let vc: setvar c
  let vs: setvar s
  let vu: setvar u
  let vv: setvar v
  let vy: setvar y
  let vd: setvar d
  let cS: class S
  let cJ: class J
  let cK: class K
  assume isf32lem.a: |- ( ph -> F : _om --> ~P G )
  assume isf32lem.b: |- ( ph -> A. x e. _om ( F ` suc x ) C_ ( F ` x ) )
  assume isf32lem.c: |- ( ph -> -. |^| ran F e. ran F )

  disjoint B x
  disjoint ph x
  disjoint A x
  disjoint F x
  disjoint a b
  disjoint a w
  disjoint a x
  disjoint B a
  disjoint b w
  disjoint b x
  disjoint B b
  disjoint w x
  disjoint B w
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
  disjoint x y
  disjoint ph y
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
  disjoint A y
  disjoint F a
  disjoint F b
  disjoint F c
  disjoint F d
  disjoint F w
  disjoint F y
  disjoint S a
  disjoint S b
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
  disjoint K a
  disjoint K b
  disjoint K s
  disjoint K t
  disjoint K x
  disjoint K y
  assert |- ( ( ( ph /\ A =/= B ) /\ ( A e. _om /\ B e. _om ) ) -> ( ( ( F ` A ) \ ( F ` suc A ) ) i^i ( ( F ` B ) \ ( F ` suc B ) ) ) = (/) )

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
    cB
    wcel
    #
    cA
    cF
    cfv
    cA
    csuc
    cF
    cfv
    cdif
    #
    cB
    cF
    cfv
    cB
    csuc
    cF
    cfv
    cdif
    #
    cin
    #
    c0
    wceq
    #
    cB
    cA
    wcel
    #
    @5
    @6
    wa
    @3
    @2
    @6
    wph
    @10
    @1
    @2
    @3
    @6
    simplrr
    @1
    @2
    @3
    @6
    simplrl
    @5
    @6
    simpr
    wph
    @0
    @4
    @6
    simplll
    @3
    @2
    wa
    @6
    wph
    wa
    wa
    @9
    @8
    @7
    cin
    c0
    @7
    @8
    incom
    wph
    vx
    cB
    cA
    cF
    cG
    isf32lem.a
    isf32lem.b
    isf32lem.c
    isf32lem3
    syl5eq
    syl22anc
    @5
    @11
    wa
    @2
    @3
    @11
    wph
    @10
    @1
    @2
    @3
    @11
    simplrl
    @1
    @2
    @3
    @11
    simplrr
    @5
    @11
    simpr
    wph
    @0
    @4
    @11
    simplll
    wph
    vx
    cA
    cB
    cF
    cG
    isf32lem.a
    isf32lem.b
    isf32lem.c
    isf32lem3
    syl22anc
    @5
    @6
    @11
    wo
    #
    @0
    wph
    @0
    @4
    simplr
    @5
    @12
    cA
    cB
    @4
    cA
    cB
    wceq
    @12
    wn
    wb
    #
    @1
    @2
    cA
    word
    cB
    word
    @13
    @3
    cA
    nnord
    cB
    nnord
    cA
    cB
    ordtri3
    syl2an
    adantl
    necon2abid
    mpbird
    mpjaodan
end
