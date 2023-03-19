include "com.mm"
include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "cfv.mm"
include "cv.mm"
include "wi.mm"
include "csuc.mm"
include "wceq.mm"
include "fveq2.mm"
include "sseq1d.mm"
include "imbi2d.mm"
include "ssid.mm"
include "2a1i.mm"
include "wral.mm"
include "suceq.mm"
include "fveq2d.mm"
include "sseq12d.mm"
include "rspcv.mm"
include "syl5.mm"
include "ad2antrr.mm"
include "sstr2.mm"
include "syl6.mm"
include "a2d.mm"
include "findsg.mm"
include "impr.mm"

theorem isf32lem1
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
  assert |- ( ( ( A e. _om /\ B e. _om ) /\ ( B C_ A /\ ph ) ) -> ( F ` A ) C_ ( F ` B ) )

  proof
    cA
    com
    wcel
    cB
    com
    wcel
    #
    wa
    cB
    cA
    wss
    wph
    cA
    cF
    cfv
    #
    cB
    cF
    cfv
    #
    wss
    #
    wph
    va
    cv
    #
    cF
    cfv
    #
    @2
    wss
    #
    wi
    wph
    @2
    @2
    wss
    #
    wi
    wph
    vb
    cv
    #
    cF
    cfv
    #
    @2
    wss
    #
    wi
    wph
    @8
    csuc
    #
    cF
    cfv
    #
    @2
    wss
    #
    wi
    wph
    @3
    wi
    va
    vb
    cA
    cB
    @4
    cB
    wceq
    #
    @6
    @7
    wph
    @14
    @5
    @2
    @2
    @4
    cB
    cF
    fveq2
    sseq1d
    imbi2d
    @4
    @8
    wceq
    #
    @6
    @10
    wph
    @15
    @5
    @9
    @2
    @4
    @8
    cF
    fveq2
    sseq1d
    imbi2d
    @4
    @11
    wceq
    #
    @6
    @13
    wph
    @16
    @5
    @12
    @2
    @4
    @11
    cF
    fveq2
    sseq1d
    imbi2d
    @4
    cA
    wceq
    #
    @6
    @3
    wph
    @17
    @5
    @1
    @2
    @4
    cA
    cF
    fveq2
    sseq1d
    imbi2d
    @7
    @0
    wph
    @2
    ssid
    2a1i
    @8
    com
    wcel
    #
    @0
    wa
    cB
    @8
    wss
    #
    wa
    #
    wph
    @10
    @13
    @20
    wph
    @12
    @9
    wss
    #
    @10
    @13
    wi
    @18
    wph
    @21
    wi
    @0
    @19
    wph
    vx
    cv
    #
    csuc
    #
    cF
    cfv
    #
    @22
    cF
    cfv
    #
    wss
    #
    vx
    com
    wral
    @18
    @21
    isf32lem.b
    @26
    @21
    vx
    @8
    com
    @22
    @8
    wceq
    #
    @24
    @12
    @25
    @9
    @27
    @23
    @11
    cF
    @22
    @8
    suceq
    fveq2d
    @22
    @8
    cF
    fveq2
    sseq12d
    rspcv
    syl5
    ad2antrr
    @12
    @9
    @2
    sstr2
    syl6
    a2d
    findsg
    impr
end
