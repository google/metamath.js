include "cioo.mm"
include "co.mm"
include "wcel.mm"
include "cr.mm"
include "cdv.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "cv.mm"
include "wrex.mm"
include "cpr.mm"
include "cun.mm"
include "wo.mm"
include "cicc.mm"
include "cxr.mm"
include "cle.mm"
include "wbr.mm"
include "rexrd.mm"
include "ltled.mm"
include "prunioo.mm"
include "syl3anc.mm"
include "eleqtrrd.mm"
include "elun.mm"
include "sylib.mm"
include "ord.mm"
include "mt3d.mm"
include "ccncf.mm"
include "wf.mm"
include "cncff.mm"
include "syl.mm"
include "wss.mm"
include "iccssre.mm"
include "syl2anc.mm"
include "ioossicc.mm"
include "a1i.mm"
include "cdm.mm"
include "wral.mm"
include "ssralv.mm"
include "sylc.mm"
include "dvferm.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "rspcev.mm"

theorem rollelem
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cU: class U
  let cF: class F
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  assume rolle.a: |- ( ph -> A e. RR )
  assume rolle.b: |- ( ph -> B e. RR )
  assume rolle.lt: |- ( ph -> A < B )
  assume rolle.f: |- ( ph -> F e. ( ( A [,] B ) -cn-> RR ) )
  assume rolle.d: |- ( ph -> dom ( RR _D F ) = ( A (,) B ) )
  assume rolle.r: |- ( ph -> A. y e. ( A [,] B ) ( F ` y ) <_ ( F ` U ) )
  assume rolle.u: |- ( ph -> U e. ( A [,] B ) )
  assume rolle.n: |- ( ph -> -. U e. { A , B } )

  disjoint x y
  disjoint A x
  disjoint A y
  disjoint ph x
  disjoint ph y
  disjoint B x
  disjoint B y
  disjoint F x
  disjoint F y
  disjoint U x
  disjoint U y
  disjoint t u
  disjoint t v
  disjoint t x
  disjoint t y
  disjoint A t
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint A u
  disjoint v x
  disjoint v y
  disjoint A v
  disjoint ph t
  disjoint ph u
  disjoint ph v
  disjoint B t
  disjoint B u
  disjoint B v
  disjoint F t
  disjoint F u
  disjoint F v
  disjoint U u
  disjoint U v
  assert |- ( ph -> E. x e. ( A (,) B ) ( ( RR _D F ) ` x ) = 0 )

  proof
    wph
    cU
    cA
    cB
    cioo
    co
    #
    wcel
    #
    cU
    cr
    cF
    cdv
    co
    #
    cfv
    #
    cc0
    wceq
    #
    vx
    cv
    #
    @2
    cfv
    #
    cc0
    wceq
    #
    vx
    @0
    wrex
    wph
    @1
    cU
    cA
    cB
    cpr
    #
    wcel
    #
    rolle.n
    wph
    @1
    @9
    wph
    cU
    @0
    @8
    cun
    #
    wcel
    @1
    @9
    wo
    wph
    cU
    cA
    cB
    cicc
    co
    #
    @10
    rolle.u
    wph
    cA
    cxr
    wcel
    cB
    cxr
    wcel
    cA
    cB
    cle
    wbr
    @10
    @11
    wceq
    wph
    cA
    rolle.a
    rexrd
    wph
    cB
    rolle.b
    rexrd
    wph
    cA
    cB
    rolle.a
    rolle.b
    rolle.lt
    ltled
    cA
    cB
    prunioo
    syl3anc
    eleqtrrd
    cU
    @0
    @8
    elun
    sylib
    ord
    mt3d
    #
    wph
    vy
    cA
    cB
    cU
    cF
    @11
    wph
    cF
    @11
    cr
    ccncf
    co
    wcel
    @11
    cr
    cF
    wf
    rolle.f
    @11
    cr
    cF
    cncff
    syl
    wph
    cA
    cr
    wcel
    cB
    cr
    wcel
    @11
    cr
    wss
    rolle.a
    rolle.b
    cA
    cB
    iccssre
    syl2anc
    @12
    @0
    @11
    wss
    #
    wph
    cA
    cB
    ioossicc
    a1i
    #
    wph
    cU
    @0
    @2
    cdm
    @12
    rolle.d
    eleqtrrd
    wph
    @13
    vy
    cv
    cF
    cfv
    cU
    cF
    cfv
    cle
    wbr
    #
    vy
    @11
    wral
    @15
    vy
    @0
    wral
    @14
    rolle.r
    @15
    vy
    @0
    @11
    ssralv
    sylc
    dvferm
    @7
    @4
    vx
    cU
    @0
    @5
    cU
    wceq
    @6
    @3
    cc0
    @5
    cU
    @2
    fveq2
    eqeq1d
    rspcev
    syl2anc
end
