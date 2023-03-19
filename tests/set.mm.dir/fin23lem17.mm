include "cv.mm"
include "crn.mm"
include "cuni.mm"
include "wcel.mm"
include "com.mm"
include "wf1.mm"
include "wa.mm"
include "cpw.mm"
include "cmap.mm"
include "co.mm"
include "csuc.mm"
include "cfv.mm"
include "wss.mm"
include "wral.mm"
include "cint.mm"
include "wi.mm"
include "wf.mm"
include "wfn.mm"
include "cvv.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "cif.mm"
include "cmpt2.mm"
include "fnseqom.mm"
include "dffn3.mm"
include "mpbi.mm"
include "pwuni.mm"
include "fin23lem16.mm"
include "pweqi.mm"
include "sseqtri.mm"
include "fss.mm"
include "mp2an.mm"
include "wb.mm"
include "vex.mm"
include "rnex.mm"
include "uniex.mm"
include "pwex.mm"
include "f1f.mm"
include "dmfex.mm"
include "sylancr.mm"
include "adantl.mm"
include "elmapg.mm"
include "mpbiri.mm"
include "isfin3ds.mm"
include "ibi.mm"
include "adantr.mm"
include "fin23lem13.mm"
include "rgen.mm"
include "a1i.mm"
include "fveq1.mm"
include "sseq12d.mm"
include "ralbidv.mm"
include "rneq.mm"
include "inteqd.mm"
include "eleq12d.mm"
include "imbi12d.mm"
include "rspcv.mm"
include "syl3c.mm"

theorem fin23lem17
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
  assert |- ( ( U. ran t e. F /\ t : _om -1-1-> V ) -> |^| ran U e. ran U )

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
    #
    cU
    @2
    cpw
    #
    com
    cmap
    co
    #
    wcel
    #
    vc
    cv
    #
    csuc
    #
    vb
    cv
    #
    cfv
    #
    @9
    @11
    cfv
    #
    wss
    #
    vc
    com
    wral
    #
    @11
    crn
    #
    cint
    #
    @16
    wcel
    #
    wi
    #
    vb
    @7
    wral
    #
    @10
    cU
    cfv
    #
    @9
    cU
    cfv
    #
    wss
    #
    vc
    com
    wral
    #
    cU
    crn
    #
    cint
    #
    @25
    wcel
    #
    @5
    @8
    com
    @6
    cU
    wf
    #
    com
    @25
    cU
    wf
    #
    @25
    @6
    wss
    @28
    cU
    com
    wfn
    @29
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
    @30
    @31
    cif
    cmpt2
    cU
    @2
    fin23lem.a
    fnseqom
    com
    cU
    dffn3
    mpbi
    @25
    @25
    cuni
    #
    cpw
    @6
    @25
    pwuni
    @32
    @2
    vu
    vt
    cU
    vi
    fin23lem.a
    fin23lem16
    pweqi
    sseqtri
    com
    @25
    @6
    cU
    fss
    mp2an
    @5
    @6
    cvv
    wcel
    com
    cvv
    wcel
    #
    @8
    @28
    wb
    @2
    @1
    @0
    vt
    vex
    #
    rnex
    uniex
    pwex
    @4
    @33
    @3
    @4
    @0
    cvv
    wcel
    com
    cV
    @0
    wf
    @33
    @34
    com
    cV
    @0
    f1f
    com
    cV
    cvv
    @0
    dmfex
    sylancr
    adantl
    @6
    com
    cU
    cvv
    cvv
    elmapg
    sylancr
    mpbiri
    @3
    @20
    @4
    @3
    @20
    vc
    @2
    vb
    vg
    cF
    cF
    va
    vx
    fin23lem17.f
    isfin3ds
    ibi
    adantr
    @24
    @5
    @23
    vc
    com
    vu
    vt
    @9
    cU
    vi
    fin23lem.a
    fin23lem13
    rgen
    a1i
    @19
    @24
    @27
    wi
    vb
    cU
    @7
    @11
    cU
    wceq
    #
    @15
    @24
    @18
    @27
    @35
    @14
    @23
    vc
    com
    @35
    @12
    @21
    @13
    @22
    @10
    @11
    cU
    fveq1
    @9
    @11
    cU
    fveq1
    sseq12d
    ralbidv
    @35
    @17
    @26
    @16
    @25
    @35
    @16
    @25
    @11
    cU
    rneq
    #
    inteqd
    @36
    eleq12d
    imbi12d
    rspcv
    syl3c
end
