include "crn.mm"
include "cuni.mm"
include "cv.mm"
include "wss.mm"
include "unissb.mm"
include "wcel.mm"
include "cfv.mm"
include "wceq.mm"
include "com.mm"
include "wrex.mm"
include "wfn.mm"
include "wb.mm"
include "cvv.mm"
include "cin.mm"
include "c0.mm"
include "cif.mm"
include "cmpt2.mm"
include "fnseqom.mm"
include "fvelrnb.mm"
include "ax-mp.mm"
include "peano1.mm"
include "wa.mm"
include "0ss.mm"
include "fin23lem15.mm"
include "mpan2.mm"
include "vex.mm"
include "rnex.mm"
include "uniex.mm"
include "seqom0g.mm"
include "syl6sseq.mm"
include "sseq1.mm"
include "syl5ibcom.mm"
include "rexlimiv.mm"
include "sylbi.mm"
include "mprgbir.mm"
include "fnfvelrn.mm"
include "mp2an.mm"
include "eqeltrri.mm"
include "elssuni.mm"
include "eqssi.mm"

theorem fin23lem16
  let vu: setvar u
  let vt: setvar t
  let cU: class U
  let vi: setvar i
  let vc: setvar c
  let vg: setvar g
  let vv: setvar v
  let vx: setvar x
  let vz: setvar z
  let va: setvar a
  let vb: setvar b
  let cA: class A
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
  disjoint A i
  disjoint A u
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
  assert |- U. ran U = U. ran t

  proof
    cU
    crn
    #
    cuni
    #
    vt
    cv
    #
    crn
    #
    cuni
    #
    @1
    @4
    wss
    va
    cv
    #
    @4
    wss
    #
    va
    @0
    va
    @0
    @4
    unissb
    @5
    @0
    wcel
    #
    vb
    cv
    #
    cU
    cfv
    #
    @5
    wceq
    #
    vb
    com
    wrex
    #
    @6
    cU
    com
    wfn
    #
    @7
    @11
    wb
    vi
    vu
    com
    cvv
    vi
    cv
    @2
    cfv
    vu
    cv
    #
    cin
    #
    c0
    wceq
    @13
    @14
    cif
    cmpt2
    #
    cU
    @4
    fin23lem.a
    fnseqom
    #
    vb
    com
    @5
    cU
    fvelrnb
    ax-mp
    @10
    @6
    vb
    com
    @8
    com
    wcel
    #
    @9
    @4
    wss
    @10
    @6
    @17
    @9
    c0
    cU
    cfv
    #
    @4
    @17
    c0
    com
    wcel
    #
    @9
    @18
    wss
    #
    peano1
    @17
    @19
    wa
    c0
    @8
    wss
    @20
    @8
    0ss
    vu
    vt
    @8
    c0
    cU
    vi
    fin23lem.a
    fin23lem15
    mpan2
    mpan2
    @4
    cvv
    wcel
    @18
    @4
    wceq
    @3
    @2
    vt
    vex
    rnex
    uniex
    @15
    cU
    @4
    cvv
    fin23lem.a
    seqom0g
    ax-mp
    #
    syl6sseq
    @9
    @5
    @4
    sseq1
    syl5ibcom
    rexlimiv
    sylbi
    mprgbir
    @4
    @0
    wcel
    @4
    @1
    wss
    @18
    @4
    @0
    @21
    @12
    @19
    @18
    @0
    wcel
    @16
    peano1
    com
    c0
    cU
    fnfvelrn
    mp2an
    eqeltrri
    @4
    @0
    elssuni
    ax-mp
    eqssi
end
