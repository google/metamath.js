include "com.mm"
include "wcel.mm"
include "csuc.mm"
include "cfv.mm"
include "cv.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "cif.mm"
include "fin23lem12.mm"
include "wss.mm"
include "sseq1.mm"
include "ssid.mm"
include "inss2.mm"
include "keephyp.mm"
include "syl6eqss.mm"

theorem fin23lem13
  let vu: setvar u
  let vt: setvar t
  let cA: class A
  let cU: class U
  let vi: setvar i
  let vc: setvar c
  let vg: setvar g
  let vv: setvar v
  let vx: setvar x
  let vz: setvar z
  let va: setvar a
  let vb: setvar b
  let cB: class B
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
  assert |- ( A e. _om -> ( U ` suc A ) C_ ( U ` A ) )

  proof
    cA
    com
    wcel
    cA
    csuc
    cU
    cfv
    cA
    vt
    cv
    cfv
    #
    cA
    cU
    cfv
    #
    cin
    #
    c0
    wceq
    #
    @1
    @2
    cif
    #
    @1
    vu
    vt
    cA
    cU
    vi
    fin23lem.a
    fin23lem12
    @3
    @1
    @1
    wss
    @2
    @1
    wss
    @4
    @1
    wss
    @1
    @2
    @1
    @4
    @1
    sseq1
    @2
    @4
    @1
    sseq1
    @1
    ssid
    @0
    @1
    inss2
    keephyp
    syl6eqss
end
