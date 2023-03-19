include "com.mm"
include "wcel.mm"
include "cv.mm"
include "crn.mm"
include "cuni.mm"
include "c0.mm"
include "wne.mm"
include "cfv.mm"
include "wi.mm"
include "csuc.mm"
include "wceq.mm"
include "fveq2.mm"
include "neeq1d.mm"
include "imbi2d.mm"
include "weq.mm"
include "cvv.mm"
include "vex.mm"
include "rnex.mm"
include "uniex.mm"
include "cin.mm"
include "cif.mm"
include "cmpt2.mm"
include "seqom0g.mm"
include "mp1i.mm"
include "id.mm"
include "eqnetrd.mm"
include "wa.mm"
include "fin23lem12.mm"
include "adantr.mm"
include "iftrue.mm"
include "simprr.mm"
include "wn.mm"
include "iffalse.mm"
include "df-ne.mm"
include "biimpri.mm"
include "pm2.61ian.mm"
include "ex.mm"
include "imim2d.mm"
include "finds.mm"
include "imp.mm"

theorem fin23lem14
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
  assert |- ( ( A e. _om /\ U. ran t =/= (/) ) -> ( U ` A ) =/= (/) )

  proof
    cA
    com
    wcel
    vt
    cv
    #
    crn
    #
    cuni
    #
    c0
    wne
    #
    cA
    cU
    cfv
    #
    c0
    wne
    #
    @3
    va
    cv
    #
    cU
    cfv
    #
    c0
    wne
    #
    wi
    @3
    c0
    cU
    cfv
    #
    c0
    wne
    #
    wi
    @3
    vb
    cv
    #
    cU
    cfv
    #
    c0
    wne
    #
    wi
    @3
    @11
    csuc
    #
    cU
    cfv
    #
    c0
    wne
    #
    wi
    @3
    @5
    wi
    va
    vb
    cA
    @6
    c0
    wceq
    #
    @8
    @10
    @3
    @17
    @7
    @9
    c0
    @6
    c0
    cU
    fveq2
    neeq1d
    imbi2d
    va
    vb
    weq
    #
    @8
    @13
    @3
    @18
    @7
    @12
    c0
    @6
    @11
    cU
    fveq2
    neeq1d
    imbi2d
    @6
    @14
    wceq
    #
    @8
    @16
    @3
    @19
    @7
    @15
    c0
    @6
    @14
    cU
    fveq2
    neeq1d
    imbi2d
    @6
    cA
    wceq
    #
    @8
    @5
    @3
    @20
    @7
    @4
    c0
    @6
    cA
    cU
    fveq2
    neeq1d
    imbi2d
    @3
    @9
    @2
    c0
    @2
    cvv
    wcel
    @9
    @2
    wceq
    @3
    @1
    @0
    vt
    vex
    rnex
    uniex
    vi
    vu
    com
    cvv
    vi
    cv
    @0
    cfv
    vu
    cv
    #
    cin
    #
    c0
    wceq
    @21
    @22
    cif
    cmpt2
    cU
    @2
    cvv
    fin23lem.a
    seqom0g
    mp1i
    @3
    id
    eqnetrd
    @11
    com
    wcel
    #
    @13
    @16
    @3
    @23
    @13
    @16
    @23
    @13
    wa
    #
    @15
    @11
    @0
    cfv
    @12
    cin
    #
    c0
    wceq
    #
    @12
    @25
    cif
    #
    c0
    @23
    @15
    @27
    wceq
    @13
    vu
    vt
    @11
    cU
    vi
    fin23lem.a
    fin23lem12
    adantr
    @26
    @24
    @27
    c0
    wne
    @26
    @24
    wa
    @27
    @12
    c0
    @26
    @27
    @12
    wceq
    @24
    @26
    @12
    @25
    iftrue
    adantr
    @26
    @23
    @13
    simprr
    eqnetrd
    @26
    wn
    #
    @24
    wa
    @27
    @25
    c0
    @28
    @27
    @25
    wceq
    @24
    @26
    @12
    @25
    iffalse
    adantr
    @28
    @25
    c0
    wne
    #
    @24
    @29
    @28
    @25
    c0
    df-ne
    biimpri
    adantr
    eqnetrd
    pm2.61ian
    eqnetrd
    ex
    imim2d
    finds
    imp
end
