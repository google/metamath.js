include "crngo.mm"
include "wcel.mm"
include "cpridl.mm"
include "cfv.mm"
include "wa.mm"
include "cidl.mm"
include "cv.mm"
include "co.mm"
include "wral.mm"
include "wss.mm"
include "wo.mm"
include "wi.mm"
include "c1st.mm"
include "crn.mm"
include "wne.mm"
include "w3a.mm"
include "eqid.mm"
include "ispridl.mm"
include "df-3an.mm"
include "syl6bb.mm"
include "simplbda.mm"
include "wceq.mm"
include "raleq.mm"
include "sseq1.mm"
include "orbi1d.mm"
include "imbi12d.mm"
include "ralbidv.mm"
include "orbi2d.mm"
include "rspc2v.mm"
include "syl5com.mm"
include "expd.mm"
include "3imp2.mm"

theorem pridl
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let cH: class H
  let va: setvar a
  let vb: setvar b
  assume pridl.1: |- H = ( 2nd ` R )

  disjoint R x
  disjoint R y
  disjoint x y
  disjoint P x
  disjoint P y
  disjoint A x
  disjoint B x
  disjoint B y
  disjoint R a
  disjoint R b
  disjoint a x
  disjoint b x
  disjoint a y
  disjoint b y
  disjoint a b
  disjoint P a
  disjoint P b
  disjoint A a
  disjoint A b
  disjoint B a
  disjoint B b
  disjoint H a
  disjoint H b
  assert |- ( ( ( R e. RingOps /\ P e. ( PrIdl ` R ) ) /\ ( A e. ( Idl ` R ) /\ B e. ( Idl ` R ) /\ A. x e. A A. y e. B ( x H y ) e. P ) ) -> ( A C_ P \/ B C_ P ) )

  proof
    cR
    crngo
    wcel
    #
    cP
    cR
    cpridl
    cfv
    wcel
    #
    wa
    #
    cA
    cR
    cidl
    cfv
    #
    wcel
    #
    cB
    @3
    wcel
    #
    vx
    cv
    vy
    cv
    cH
    co
    cP
    wcel
    #
    vy
    cB
    wral
    #
    vx
    cA
    wral
    #
    cA
    cP
    wss
    #
    cB
    cP
    wss
    #
    wo
    #
    @2
    @4
    @5
    @8
    @11
    wi
    #
    @2
    @6
    vy
    vb
    cv
    #
    wral
    #
    vx
    va
    cv
    #
    wral
    #
    @15
    cP
    wss
    #
    @13
    cP
    wss
    #
    wo
    #
    wi
    #
    vb
    @3
    wral
    va
    @3
    wral
    #
    @4
    @5
    wa
    @12
    @0
    @1
    cP
    @3
    wcel
    #
    cP
    cR
    c1st
    cfv
    #
    crn
    #
    wne
    #
    wa
    #
    @21
    @0
    @1
    @22
    @25
    @21
    w3a
    @26
    @21
    wa
    vx
    vy
    cP
    cR
    @23
    cH
    @24
    va
    vb
    @23
    eqid
    pridl.1
    @24
    eqid
    ispridl
    @22
    @25
    @21
    df-3an
    syl6bb
    simplbda
    @20
    @12
    @14
    vx
    cA
    wral
    #
    @9
    @18
    wo
    #
    wi
    va
    vb
    cA
    cB
    @3
    @3
    @15
    cA
    wceq
    #
    @16
    @27
    @19
    @28
    @14
    vx
    @15
    cA
    raleq
    @29
    @17
    @9
    @18
    @15
    cA
    cP
    sseq1
    orbi1d
    imbi12d
    @13
    cB
    wceq
    #
    @27
    @8
    @28
    @11
    @30
    @14
    @7
    vx
    cA
    @6
    vy
    @13
    cB
    raleq
    ralbidv
    @30
    @18
    @10
    @9
    @13
    cB
    cP
    sseq1
    orbi2d
    imbi12d
    rspc2v
    syl5com
    expd
    3imp2
end
