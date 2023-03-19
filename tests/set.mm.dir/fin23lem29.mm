include "cfn.mm"
include "wcel.mm"
include "cv.mm"
include "ccom.mm"
include "cfv.mm"
include "crn.mm"
include "cint.mm"
include "cdif.mm"
include "cmpt.mm"
include "cif.mm"
include "wceq.mm"
include "wa.mm"
include "wn.mm"
include "wo.mm"
include "cuni.mm"
include "wss.mm"
include "eqif.mm"
include "biimpi.mm"
include "rneq.mm"
include "unieqd.mm"
include "rncoss.mm"
include "unissi.mm"
include "syl6eqss.mm"
include "adantl.mm"
include "unissb.mm"
include "wrex.mm"
include "cab.mm"
include "abid.mm"
include "fvssunirn.mm"
include "a1i.mm"
include "ssdifssd.mm"
include "sseq1.mm"
include "syl5ibrcom.mm"
include "rexlimiv.mm"
include "sylbi.mm"
include "eqid.mm"
include "rnmpt.mm"
include "eleq2s.mm"
include "mprgbir.mm"
include "sstri.mm"
include "jaoi.mm"
include "mp2b.mm"

theorem fin23lem29
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
  let cZ: class Z
  let va: setvar a
  let vc: setvar c
  let vb: setvar b
  let cA: class A
  let cB: class B
  let cV: class V
  let vf: setvar f
  let cG: class G
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
  disjoint V a
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
  assert |- U. ran Z C_ U. ran t

  proof
    cZ
    cP
    cfn
    wcel
    #
    vt
    cv
    #
    cR
    ccom
    #
    vz
    cP
    vz
    cv
    #
    @1
    cfv
    #
    cU
    crn
    cint
    #
    cdif
    #
    cmpt
    #
    cQ
    ccom
    #
    cif
    wceq
    #
    @0
    cZ
    @2
    wceq
    #
    wa
    #
    @0
    wn
    #
    cZ
    @8
    wceq
    #
    wa
    #
    wo
    #
    cZ
    crn
    #
    cuni
    #
    @1
    crn
    #
    cuni
    #
    wss
    #
    fin23lem.e
    @9
    @15
    @0
    cZ
    @2
    @8
    eqif
    biimpi
    @11
    @20
    @14
    @10
    @20
    @0
    @10
    @17
    @2
    crn
    #
    cuni
    @19
    @10
    @16
    @21
    cZ
    @2
    rneq
    unieqd
    @21
    @18
    @1
    cR
    rncoss
    unissi
    syl6eqss
    adantl
    @13
    @20
    @12
    @13
    @17
    @8
    crn
    #
    cuni
    #
    @19
    @13
    @16
    @22
    cZ
    @8
    rneq
    unieqd
    @23
    @7
    crn
    #
    cuni
    #
    @19
    @22
    @24
    @7
    cQ
    rncoss
    unissi
    @25
    @19
    wss
    va
    cv
    #
    @19
    wss
    #
    va
    @24
    va
    @24
    @19
    unissb
    @27
    @26
    @26
    @6
    wceq
    #
    vz
    cP
    wrex
    #
    va
    cab
    #
    @24
    @26
    @30
    wcel
    @29
    @27
    @29
    va
    abid
    @28
    @27
    vz
    cP
    @3
    cP
    wcel
    #
    @27
    @28
    @6
    @19
    wss
    @31
    @4
    @19
    @5
    @4
    @19
    wss
    @31
    @1
    @3
    fvssunirn
    a1i
    ssdifssd
    @26
    @6
    @19
    sseq1
    syl5ibrcom
    rexlimiv
    sylbi
    vz
    va
    cP
    @6
    @7
    @7
    eqid
    rnmpt
    eleq2s
    mprgbir
    sstri
    syl6eqss
    adantl
    jaoi
    mp2b
end
