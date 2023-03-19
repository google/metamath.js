include "cv.mm"
include "crn.mm"
include "cuni.mm"
include "wcel.mm"
include "com.mm"
include "wf1.mm"
include "wa.mm"
include "cint.mm"
include "c0.mm"
include "wne.mm"
include "fin23lem17.mm"
include "wi.mm"
include "cfv.mm"
include "wceq.mm"
include "wrex.mm"
include "wfn.mm"
include "wb.mm"
include "cvv.mm"
include "cin.mm"
include "cif.mm"
include "cmpt2.mm"
include "fnseqom.mm"
include "fvelrnb.mm"
include "ax-mp.mm"
include "id.mm"
include "csn.mm"
include "cdif.mm"
include "cen.mm"
include "wbr.mm"
include "cfn.mm"
include "wn.mm"
include "wf1o.mm"
include "vex.mm"
include "f1f1orn.mm"
include "f1oen3g.mm"
include "sylancr.mm"
include "ominf.mm"
include "wss.mm"
include "ssdif0.mm"
include "snfi.mm"
include "ssfi.mm"
include "mpan.mm"
include "enfi.mm"
include "syl5ibr.mm"
include "syl5bir.mm"
include "necon3bd.mm"
include "mpisyl.mm"
include "wex.mm"
include "n0.mm"
include "eldifsn.mm"
include "elssuni.mm"
include "ssn0.mm"
include "sylan.mm"
include "sylbi.mm"
include "exlimiv.mm"
include "syl.mm"
include "fin23lem14.mm"
include "syl2anr.mm"
include "neeq1.mm"
include "syl5ibcom.mm"
include "rexlimdva.mm"
include "syl5bi.mm"
include "adantl.mm"
include "mpd.mm"

theorem fin23lem21
  let vx: setvar x
  let vu: setvar u
  let vt: setvar t
  let cU: class U
  let vg: setvar g
  let vi: setvar i
  let cF: class F
  let cV: class V
  let va: setvar a
  let vc: setvar c
  let vv: setvar v
  let vz: setvar z
  let vb: setvar b
  let cA: class A
  let cB: class B
  let vw: setvar w
  let cP: class P
  let cR: class R
  let vf: setvar f
  let cZ: class Z
  let cG: class G
  assume fin23lem.a: |- U = seqom ( ( i e. _om , u e. _V |-> if ( ( ( t ` i ) i^i u ) = (/) , u , ( ( t ` i ) i^i u ) ) ) , U. ran t )
  assume fin23lem17.f: |- F = { g | A. a e. ( ~P g ^m _om ) ( A. x e. _om ( a ` suc x ) C_ ( a ` x ) -> |^| ran a e. ran a ) }

  disjoint g i
  disjoint g t
  disjoint g u
  disjoint g x
  disjoint i t
  disjoint i u
  disjoint i x
  disjoint t u
  disjoint t x
  disjoint u x
  disjoint a i
  disjoint a u
  disjoint a t
  disjoint F a
  disjoint F t
  disjoint V a
  disjoint a x
  disjoint U a
  disjoint U i
  disjoint U u
  disjoint a g
  disjoint c g
  disjoint c i
  disjoint c t
  disjoint c u
  disjoint c v
  disjoint c x
  disjoint c z
  disjoint g v
  disjoint g z
  disjoint i v
  disjoint i z
  disjoint t v
  disjoint t z
  disjoint u v
  disjoint u z
  disjoint v x
  disjoint v z
  disjoint x z
  disjoint a b
  disjoint A a
  disjoint b i
  disjoint b u
  disjoint A b
  disjoint A i
  disjoint A u
  disjoint B a
  disjoint B b
  disjoint a w
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
  assert |- ( ( U. ran t e. F /\ t : _om -1-1-> V ) -> |^| ran U =/= (/) )

  proof
    vt
    cv
    #
    crn
    #
    cuni
    #
    cF
    wcel
    #
    com
    cV
    @0
    wf1
    #
    wa
    cU
    crn
    #
    cint
    #
    @5
    wcel
    #
    @6
    c0
    wne
    #
    vx
    vu
    vt
    cU
    vg
    vi
    cF
    cV
    va
    fin23lem.a
    fin23lem17.f
    fin23lem17
    @4
    @7
    @8
    wi
    @3
    @7
    va
    cv
    #
    cU
    cfv
    #
    @6
    wceq
    #
    va
    com
    wrex
    #
    @4
    @8
    cU
    com
    wfn
    @7
    @12
    wb
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
    @13
    @14
    cif
    cmpt2
    cU
    @2
    fin23lem.a
    fnseqom
    va
    com
    @6
    cU
    fvelrnb
    ax-mp
    @4
    @11
    @8
    va
    com
    @4
    @9
    com
    wcel
    #
    wa
    @10
    c0
    wne
    #
    @11
    @8
    @15
    @15
    @2
    c0
    wne
    #
    @16
    @4
    @15
    id
    @4
    @1
    c0
    csn
    #
    cdif
    #
    c0
    wne
    #
    @17
    @4
    com
    @1
    cen
    wbr
    #
    com
    cfn
    wcel
    #
    wn
    @20
    @4
    @0
    cvv
    wcel
    com
    @1
    @0
    wf1o
    @21
    vt
    vex
    com
    cV
    @0
    f1f1orn
    com
    @1
    @0
    cvv
    f1oen3g
    sylancr
    ominf
    @21
    @22
    @19
    c0
    @19
    c0
    wceq
    @1
    @18
    wss
    #
    @21
    @22
    @1
    @18
    ssdif0
    @23
    @22
    @21
    @1
    cfn
    wcel
    #
    @18
    cfn
    wcel
    @23
    @24
    c0
    snfi
    @18
    @1
    ssfi
    mpan
    com
    @1
    enfi
    syl5ibr
    syl5bir
    necon3bd
    mpisyl
    @20
    @9
    @19
    wcel
    #
    va
    wex
    @17
    va
    @19
    n0
    @25
    @17
    va
    @25
    @9
    @1
    wcel
    #
    @9
    c0
    wne
    #
    wa
    @17
    @9
    @1
    c0
    eldifsn
    @26
    @9
    @2
    wss
    @27
    @17
    @9
    @1
    elssuni
    @9
    @2
    ssn0
    sylan
    sylbi
    exlimiv
    sylbi
    syl
    vu
    vt
    @9
    cU
    vi
    fin23lem.a
    fin23lem14
    syl2anr
    @10
    @6
    c0
    neeq1
    syl5ibcom
    rexlimdva
    syl5bi
    adantl
    mpd
end
