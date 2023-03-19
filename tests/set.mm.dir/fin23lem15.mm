include "cv.mm"
include "cfv.mm"
include "wss.mm"
include "csuc.mm"
include "wceq.mm"
include "fveq2.mm"
include "sseq1d.mm"
include "weq.mm"
include "com.mm"
include "wcel.mm"
include "ssid.mm"
include "a1i.mm"
include "wa.mm"
include "wi.mm"
include "fin23lem13.mm"
include "ad2antrr.mm"
include "sstr2.mm"
include "syl.mm"
include "findsg.mm"

theorem fin23lem15
  let vu: setvar u
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cU: class U
  let vi: setvar i
  let vc: setvar c
  let vg: setvar g
  let vv: setvar v
  let vx: setvar x
  let vz: setvar z
  let va: setvar a
  let vb: setvar b
  let cF: class F
  let cV: class V
  let vw: setvar w
  let cP: class P
  let cR: class R
  let vf: setvar f
  let cZ: class Z
  let cG: class G
  assume fin23lem.a: |- U = seqom ( ( i e. _om , u e. _V |-> if ( ( ( t ` i ) i^i u ) = (/) , u , ( ( t ` i ) i^i u ) ) ) , U. ran t )

  disjoint i t
  disjoint i u
  disjoint t u
  disjoint A i
  disjoint A u
  disjoint U i
  disjoint U u
  disjoint c g
  disjoint c i
  disjoint c t
  disjoint c u
  disjoint c v
  disjoint c x
  disjoint c z
  disjoint g i
  disjoint g t
  disjoint g u
  disjoint g v
  disjoint g x
  disjoint g z
  disjoint i v
  disjoint i x
  disjoint i z
  disjoint t v
  disjoint t x
  disjoint t z
  disjoint u v
  disjoint u x
  disjoint u z
  disjoint v x
  disjoint v z
  disjoint x z
  disjoint a b
  disjoint a i
  disjoint a u
  disjoint A a
  disjoint b i
  disjoint b u
  disjoint A b
  disjoint B a
  disjoint B b
  disjoint a t
  disjoint F a
  disjoint F t
  disjoint V a
  disjoint a w
  disjoint a x
  disjoint a z
  disjoint P a
  disjoint b w
  disjoint b x
  disjoint b z
  disjoint P b
  disjoint w x
  disjoint w z
  disjoint P w
  disjoint P x
  disjoint P z
  disjoint a v
  disjoint R a
  disjoint b v
  disjoint R b
  disjoint R i
  disjoint R u
  disjoint R v
  disjoint a c
  disjoint U a
  disjoint b c
  disjoint U b
  disjoint U c
  disjoint U v
  disjoint U z
  disjoint a f
  disjoint Z a
  disjoint b f
  disjoint Z b
  disjoint Z f
  disjoint a g
  disjoint G a
  disjoint b g
  disjoint b t
  disjoint G b
  disjoint f g
  disjoint f t
  disjoint f x
  disjoint G f
  disjoint G g
  disjoint G t
  disjoint G x
  assert |- ( ( ( A e. _om /\ B e. _om ) /\ B C_ A ) -> ( U ` A ) C_ ( U ` B ) )

  proof
    vb
    cv
    #
    cU
    cfv
    #
    cB
    cU
    cfv
    #
    wss
    @2
    @2
    wss
    #
    va
    cv
    #
    cU
    cfv
    #
    @2
    wss
    #
    @4
    csuc
    #
    cU
    cfv
    #
    @2
    wss
    #
    cA
    cU
    cfv
    #
    @2
    wss
    vb
    va
    cA
    cB
    @0
    cB
    wceq
    @1
    @2
    @2
    @0
    cB
    cU
    fveq2
    sseq1d
    vb
    va
    weq
    @1
    @5
    @2
    @0
    @4
    cU
    fveq2
    sseq1d
    @0
    @7
    wceq
    @1
    @8
    @2
    @0
    @7
    cU
    fveq2
    sseq1d
    @0
    cA
    wceq
    @1
    @10
    @2
    @0
    cA
    cU
    fveq2
    sseq1d
    @3
    cB
    com
    wcel
    #
    @2
    ssid
    a1i
    @4
    com
    wcel
    #
    @11
    wa
    cB
    @4
    wss
    #
    wa
    @8
    @5
    wss
    #
    @6
    @9
    wi
    @12
    @14
    @11
    @13
    vu
    vt
    @4
    cU
    vi
    fin23lem.a
    fin23lem13
    ad2antrr
    @8
    @5
    @2
    sstr2
    syl
    findsg
end
