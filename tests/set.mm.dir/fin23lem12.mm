include "com.mm"
include "wcel.mm"
include "csuc.mm"
include "cfv.mm"
include "cvv.mm"
include "cv.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "cif.mm"
include "cmpt2.mm"
include "co.mm"
include "crn.mm"
include "cuni.mm"
include "seqomsuc.mm"
include "fvex.mm"
include "fveq2.mm"
include "ineq1d.mm"
include "eqeq1d.mm"
include "ifbieq2d.mm"
include "ineq2.mm"
include "id.mm"
include "ifbieq12d.mm"
include "eqid.mm"
include "inex2.mm"
include "ifex.mm"
include "ovmpt2.mm"
include "mpan2.mm"
include "eqtrd.mm"

theorem fin23lem12
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
  assert |- ( A e. _om -> ( U ` suc A ) = if ( ( ( t ` A ) i^i ( U ` A ) ) = (/) , ( U ` A ) , ( ( t ` A ) i^i ( U ` A ) ) ) )

  proof
    cA
    com
    wcel
    #
    cA
    csuc
    cU
    cfv
    cA
    cA
    cU
    cfv
    #
    vi
    vu
    com
    cvv
    vi
    cv
    #
    vt
    cv
    #
    cfv
    #
    vu
    cv
    #
    cin
    #
    c0
    wceq
    #
    @5
    @6
    cif
    #
    cmpt2
    #
    co
    #
    cA
    @3
    cfv
    #
    @1
    cin
    #
    c0
    wceq
    #
    @1
    @12
    cif
    #
    cA
    @9
    cU
    @3
    crn
    cuni
    fin23lem.a
    seqomsuc
    @0
    @1
    cvv
    wcel
    @10
    @14
    wceq
    cA
    cU
    fvex
    #
    vi
    vu
    cA
    @1
    com
    cvv
    @8
    @14
    @9
    @11
    @5
    cin
    #
    c0
    wceq
    #
    @5
    @16
    cif
    @2
    cA
    wceq
    #
    @7
    @17
    @6
    @16
    @5
    @18
    @6
    @16
    c0
    @18
    @4
    @11
    @5
    @2
    cA
    @3
    fveq2
    ineq1d
    #
    eqeq1d
    @19
    ifbieq2d
    @5
    @1
    wceq
    #
    @17
    @13
    @5
    @16
    @1
    @12
    @20
    @16
    @12
    c0
    @5
    @1
    @11
    ineq2
    #
    eqeq1d
    @20
    id
    @21
    ifbieq12d
    @9
    eqid
    @13
    @1
    @12
    @15
    @1
    @11
    @15
    inex2
    ifex
    ovmpt2
    mpan2
    eqtrd
end
