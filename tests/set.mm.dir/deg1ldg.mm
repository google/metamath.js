include "crg.mm"
include "wcel.mm"
include "wne.mm"
include "w3a.mm"
include "cv.mm"
include "cfv.mm"
include "cn0.mm"
include "c1o.mm"
include "cmap.mm"
include "co.mm"
include "c0.mm"
include "cmpt.mm"
include "wceq.mm"
include "wa.mm"
include "wrex.mm"
include "cmpl.mm"
include "deg1fval.mm"
include "eqid.mm"
include "cps1.mm"
include "ply1bas.mm"
include "psr1baslem.mm"
include "tdeglem2.mm"
include "ply1mpl0.mm"
include "mdegldg.mm"
include "fvcoe1.mm"
include "3ad2antl2.mm"
include "fveq1.mm"
include "fvex.mm"
include "fvmpt.mm"
include "fveq2d.mm"
include "adantl.mm"
include "eqtr4d.mm"
include "neeq1d.mm"
include "anbi1d.mm"
include "ancom.mm"
include "syl6bb.mm"
include "rexbidva.mm"
include "wf1o.mm"
include "wfo.mm"
include "wb.mm"
include "df1o2.mm"
include "nn0ex.mm"
include "0ex.mm"
include "mapsnf1o2.mm"
include "f1ofo.mm"
include "eqeq1.mm"
include "fveq2.mm"
include "anbi12d.mm"
include "cbvexfo.mm"
include "mp2b.mm"
include "deg1nn0cl.mm"
include "ceqsrexv.mm"
include "syl.mm"
include "bitrd.mm"
include "mpbid.mm"

theorem deg1ldg
  let cA: class A
  let cB: class B
  let cD: class D
  let cP: class P
  let cR: class R
  let cF: class F
  let cY: class Y
  let c.0: class .0.
  let vb: setvar b
  let vd: setvar d
  let va: setvar a
  let vc: setvar c
  assume deg1z.d: |- D = ( deg1 ` R )
  assume deg1z.p: |- P = ( Poly1 ` R )
  assume deg1z.z: |- .0. = ( 0g ` P )
  assume deg1nn0cl.b: |- B = ( Base ` P )
  assume deg1ldg.y: |- Y = ( 0g ` R )
  assume deg1ldg.a: |- A = ( coe1 ` F )


  assert |- ( ( R e. Ring /\ F e. B /\ F =/= .0. ) -> ( A ` ( D ` F ) ) =/= Y )

  proof
    cR
    crg
    wcel
    #
    cF
    cB
    wcel
    #
    cF
    c.0
    wne
    #
    w3a
    #
    vb
    cv
    #
    cF
    cfv
    #
    cY
    wne
    #
    @4
    va
    cn0
    c1o
    cmap
    co
    #
    c0
    va
    cv
    #
    cfv
    #
    cmpt
    #
    cfv
    #
    cF
    cD
    cfv
    #
    wceq
    #
    wa
    #
    vb
    @7
    wrex
    #
    @12
    cA
    cfv
    #
    cY
    wne
    #
    vb
    @7
    cB
    cD
    c1o
    cR
    cmpl
    co
    #
    cR
    va
    vc
    cF
    @10
    c1o
    c.0
    cY
    cD
    cR
    deg1z.d
    deg1fval
    @18
    eqid
    #
    cP
    cR
    cR
    cps1
    cfv
    #
    cB
    deg1z.p
    @20
    eqid
    deg1nn0cl.b
    ply1bas
    deg1ldg.y
    vc
    psr1baslem
    va
    tdeglem2
    cP
    cR
    @18
    c.0
    @19
    deg1z.p
    deg1z.z
    ply1mpl0
    mdegldg
    @3
    @15
    vd
    cv
    #
    @12
    wceq
    #
    @21
    cA
    cfv
    #
    cY
    wne
    #
    wa
    #
    vd
    cn0
    wrex
    #
    @17
    @3
    @15
    @13
    @11
    cA
    cfv
    #
    cY
    wne
    #
    wa
    #
    vb
    @7
    wrex
    #
    @26
    @3
    @14
    @29
    vb
    @7
    @3
    @4
    @7
    wcel
    #
    wa
    #
    @14
    @28
    @13
    wa
    @29
    @32
    @6
    @28
    @13
    @32
    @5
    @27
    cY
    @32
    @5
    c0
    @4
    cfv
    #
    cA
    cfv
    #
    @27
    @1
    @0
    @31
    @5
    @34
    wceq
    @2
    cA
    cF
    cB
    @4
    deg1ldg.a
    fvcoe1
    3ad2antl2
    @31
    @27
    @34
    wceq
    @3
    @31
    @11
    @33
    cA
    va
    @4
    @9
    @33
    @7
    @10
    c0
    @8
    @4
    fveq1
    @10
    eqid
    #
    c0
    @4
    fvex
    fvmpt
    fveq2d
    adantl
    eqtr4d
    neeq1d
    anbi1d
    @28
    @13
    ancom
    syl6bb
    rexbidva
    @7
    cn0
    @10
    wf1o
    @7
    cn0
    @10
    wfo
    @30
    @26
    wb
    va
    cn0
    c1o
    @10
    c0
    df1o2
    nn0ex
    0ex
    @35
    mapsnf1o2
    @7
    cn0
    @10
    f1ofo
    @29
    @25
    vb
    vd
    @7
    cn0
    @10
    @11
    @21
    wceq
    #
    @13
    @22
    @28
    @24
    @11
    @21
    @12
    eqeq1
    @36
    @27
    @23
    cY
    @11
    @21
    cA
    fveq2
    neeq1d
    anbi12d
    cbvexfo
    mp2b
    syl6bb
    @3
    @12
    cn0
    wcel
    @26
    @17
    wb
    cB
    cD
    cP
    cR
    cF
    c.0
    deg1z.d
    deg1z.p
    deg1z.z
    deg1nn0cl.b
    deg1nn0cl
    @24
    @17
    vd
    @12
    cn0
    @22
    @23
    @16
    cY
    @21
    @12
    cA
    fveq2
    neeq1d
    ceqsrexv
    syl
    bitrd
    mpbid
end
