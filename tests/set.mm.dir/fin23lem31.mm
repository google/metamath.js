include "com.mm"
include "cv.mm"
include "wf1.mm"
include "wcel.mm"
include "crn.mm"
include "cuni.mm"
include "wss.mm"
include "wpss.mm"
include "wa.mm"
include "ssfin3ds.mm"
include "wne.mm"
include "fin23lem29.mm"
include "a1i.mm"
include "cint.mm"
include "c0.mm"
include "wex.mm"
include "fin23lem21.mm"
include "ancoms.mm"
include "n0.mm"
include "sylib.mm"
include "wn.mm"
include "cdm.mm"
include "wfn.mm"
include "wceq.mm"
include "cvv.mm"
include "cfv.mm"
include "cin.mm"
include "cif.mm"
include "cmpt2.mm"
include "fnseqom.mm"
include "fndm.mm"
include "ax-mp.mm"
include "peano1.mm"
include "ne0ii.mm"
include "eqnetri.mm"
include "dm0rn0.mm"
include "necon3bii.mm"
include "mpbi.mm"
include "intssuni.mm"
include "fin23lem16.mm"
include "sseqtri.mm"
include "sseli.mm"
include "adantl.mm"
include "wral.mm"
include "wi.mm"
include "wfun.mm"
include "f1fun.mm"
include "adantr.mm"
include "fin23lem30.mm"
include "syl.mm"
include "disj.mm"
include "rsp.mm"
include "con2d.mm"
include "imp.mm"
include "nelne1.mm"
include "syl2anc.mm"
include "necomd.mm"
include "exlimddv.mm"
include "df-pss.mm"
include "sylanbrc.mm"
include "sylan2.mm"
include "3impb.mm"

theorem fin23lem31
  let vx: setvar x
  let vz: setvar z
  let vw: setvar w
  let vv: setvar v
  let vu: setvar u
  let vt: setvar t
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cU: class U
  let vg: setvar g
  let vi: setvar i
  let cF: class F
  let cG: class G
  let cV: class V
  let cZ: class Z
  let va: setvar a
  let vc: setvar c
  let vb: setvar b
  let cA: class A
  let cB: class B
  let vf: setvar f
  assume fin23lem.a: |- U = seqom ( ( i e. _om , u e. _V |-> if ( ( ( t ` i ) i^i u ) = (/) , u , ( ( t ` i ) i^i u ) ) ) , U. ran t )
  assume fin23lem17.f: |- F = { g | A. a e. ( ~P g ^m _om ) ( A. x e. _om ( a ` suc x ) C_ ( a ` x ) -> |^| ran a e. ran a ) }
  assume fin23lem.b: |- P = { v e. _om | |^| ran U C_ ( t ` v ) }
  assume fin23lem.c: |- Q = ( w e. _om |-> ( iota_ x e. P ( x i^i P ) ~~ w ) )
  assume fin23lem.d: |- R = ( w e. _om |-> ( iota_ x e. ( _om \ P ) ( x i^i ( _om \ P ) ) ~~ w ) )
  assume fin23lem.e: |- Z = if ( P e. Fin , ( t o. R ) , ( ( z e. P |-> ( ( t ` z ) \ |^| ran U ) ) o. Q ) )

  disjoint g i
  disjoint g t
  disjoint g u
  disjoint g v
  disjoint g x
  disjoint g z
  disjoint i t
  disjoint i u
  disjoint i v
  disjoint i x
  disjoint i z
  disjoint t u
  disjoint t v
  disjoint t x
  disjoint t z
  disjoint u v
  disjoint u x
  disjoint u z
  disjoint v x
  disjoint v z
  disjoint x z
  disjoint a i
  disjoint a u
  disjoint a t
  disjoint F a
  disjoint F t
  disjoint V a
  disjoint a w
  disjoint a x
  disjoint a z
  disjoint P a
  disjoint w x
  disjoint w z
  disjoint P w
  disjoint P x
  disjoint P z
  disjoint a v
  disjoint R a
  disjoint R i
  disjoint R u
  disjoint R v
  disjoint U a
  disjoint U i
  disjoint U u
  disjoint U v
  disjoint U z
  disjoint Z a
  disjoint a g
  disjoint G a
  disjoint G g
  disjoint G t
  disjoint G x
  disjoint c g
  disjoint c i
  disjoint c t
  disjoint c u
  disjoint c v
  disjoint c x
  disjoint c z
  disjoint a b
  disjoint A a
  disjoint b i
  disjoint b u
  disjoint A b
  disjoint A i
  disjoint A u
  disjoint B a
  disjoint B b
  disjoint b w
  disjoint b x
  disjoint b z
  disjoint P b
  disjoint b v
  disjoint R b
  disjoint a c
  disjoint b c
  disjoint U b
  disjoint U c
  disjoint a f
  disjoint b f
  disjoint Z b
  disjoint Z f
  disjoint b g
  disjoint b t
  disjoint G b
  disjoint f g
  disjoint f t
  disjoint f x
  disjoint G f
  assert |- ( ( t : _om -1-1-> V /\ G e. F /\ U. ran t C_ G ) -> U. ran Z C. U. ran t )

  proof
    com
    cV
    vt
    cv
    #
    wf1
    #
    cG
    cF
    wcel
    #
    @0
    crn
    cuni
    #
    cG
    wss
    #
    cZ
    crn
    cuni
    #
    @3
    wpss
    #
    @2
    @4
    wa
    @1
    @3
    cF
    wcel
    #
    @6
    cG
    @3
    vg
    cF
    va
    vx
    fin23lem17.f
    ssfin3ds
    @1
    @7
    wa
    #
    @5
    @3
    wss
    #
    @5
    @3
    wne
    #
    @6
    @9
    @8
    vx
    vz
    vw
    vv
    vu
    vt
    cP
    cQ
    cR
    cU
    vg
    vi
    cF
    cZ
    va
    fin23lem.a
    fin23lem17.f
    fin23lem.b
    fin23lem.c
    fin23lem.d
    fin23lem.e
    fin23lem29
    a1i
    @8
    va
    cv
    #
    cU
    crn
    #
    cint
    #
    wcel
    #
    @10
    va
    @8
    @13
    c0
    wne
    #
    @14
    va
    wex
    @7
    @1
    @15
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
    fin23lem21
    ancoms
    va
    @13
    n0
    sylib
    @8
    @14
    wa
    #
    @3
    @5
    @16
    @11
    @3
    wcel
    #
    @11
    @5
    wcel
    #
    wn
    #
    @3
    @5
    wne
    @14
    @17
    @8
    @13
    @3
    @11
    @13
    @12
    cuni
    #
    @3
    @12
    c0
    wne
    #
    @13
    @20
    wss
    cU
    cdm
    #
    c0
    wne
    @21
    @22
    com
    c0
    cU
    com
    wfn
    @22
    com
    wceq
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
    @23
    @24
    cif
    cmpt2
    cU
    @3
    fin23lem.a
    fnseqom
    com
    cU
    fndm
    ax-mp
    c0
    com
    peano1
    ne0ii
    eqnetri
    @22
    c0
    @12
    c0
    cU
    dm0rn0
    necon3bii
    mpbi
    @12
    intssuni
    ax-mp
    vu
    vt
    cU
    vi
    fin23lem.a
    fin23lem16
    sseqtri
    sseli
    adantl
    @8
    @14
    @19
    @8
    @18
    @14
    @8
    @14
    wn
    #
    va
    @5
    wral
    #
    @18
    @25
    wi
    @8
    @5
    @13
    cin
    c0
    wceq
    #
    @26
    @8
    @0
    wfun
    #
    @27
    @1
    @28
    @7
    com
    cV
    @0
    f1fun
    adantr
    vx
    vz
    vw
    vv
    vu
    vt
    cP
    cQ
    cR
    cU
    vg
    vi
    cF
    cZ
    va
    fin23lem.a
    fin23lem17.f
    fin23lem.b
    fin23lem.c
    fin23lem.d
    fin23lem.e
    fin23lem30
    syl
    va
    @5
    @13
    disj
    sylib
    @25
    va
    @5
    rsp
    syl
    con2d
    imp
    @11
    @3
    @5
    nelne1
    syl2anc
    necomd
    exlimddv
    @5
    @3
    df-pss
    sylanbrc
    sylan2
    3impb
end
