include "com.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "csuc.mm"
include "cdif.mm"
include "wn.mm"
include "wral.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "eldifi.mm"
include "wss.mm"
include "simpll.mm"
include "peano2.mm"
include "ad2antlr.mm"
include "word.mm"
include "nnord.mm"
include "ad2antrr.mm"
include "simprl.mm"
include "ordsucss.mm"
include "sylc.mm"
include "simprr.mm"
include "isf32lem1.mm"
include "syl22anc.mm"
include "sseld.mm"
include "elndif.mm"
include "syl56.mm"
include "ralrimiv.mm"
include "disj.mm"
include "sylibr.mm"

theorem isf32lem3
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
  assert |- ( ( ( A e. _om /\ B e. _om ) /\ ( B e. A /\ ph ) ) -> ( ( ( F ` A ) \ ( F ` suc A ) ) i^i ( ( F ` B ) \ ( F ` suc B ) ) ) = (/) )

  proof
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
    cB
    cA
    wcel
    #
    wph
    wa
    #
    wa
    #
    va
    cv
    #
    cB
    cF
    cfv
    #
    cB
    csuc
    #
    cF
    cfv
    #
    cdif
    #
    wcel
    wn
    #
    va
    cA
    cF
    cfv
    #
    cA
    csuc
    cF
    cfv
    #
    cdif
    #
    wral
    @14
    @10
    cin
    c0
    wceq
    @5
    @11
    va
    @14
    @6
    @14
    wcel
    @6
    @12
    wcel
    @5
    @6
    @9
    wcel
    @11
    @6
    @12
    @13
    eldifi
    @5
    @12
    @9
    @6
    @5
    @0
    @8
    com
    wcel
    #
    @8
    cA
    wss
    #
    wph
    @12
    @9
    wss
    @0
    @1
    @4
    simpll
    @1
    @15
    @0
    @4
    cB
    peano2
    ad2antlr
    @5
    cA
    word
    #
    @3
    @16
    @0
    @17
    @1
    @4
    cA
    nnord
    ad2antrr
    @2
    @3
    wph
    simprl
    cB
    cA
    ordsucss
    sylc
    @2
    @3
    wph
    simprr
    wph
    vx
    cA
    @8
    cF
    cG
    isf32lem.a
    isf32lem.b
    isf32lem.c
    isf32lem1
    syl22anc
    sseld
    @6
    @9
    @7
    elndif
    syl56
    ralrimiv
    va
    @14
    @10
    disj
    sylibr
end
