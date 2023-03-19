include "wcel.mm"
include "cxr.mm"
include "wa.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cv.mm"
include "cn0.mm"
include "c1o.mm"
include "cmap.mm"
include "co.mm"
include "c0.mm"
include "cmpt.mm"
include "clt.mm"
include "wceq.mm"
include "wi.mm"
include "wral.mm"
include "cmpl.mm"
include "deg1fval.mm"
include "eqid.mm"
include "cps1.mm"
include "ply1bas.mm"
include "psr1baslem.mm"
include "tdeglem2.mm"
include "mdegleb.mm"
include "wf1o.mm"
include "wfo.mm"
include "wb.mm"
include "df1o2.mm"
include "nn0ex.mm"
include "0ex.mm"
include "mapsnf1o2.mm"
include "f1ofo.mm"
include "breq2.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "imbi12d.mm"
include "cbvfo.mm"
include "mp2b.mm"
include "fveq1.mm"
include "fvex.mm"
include "fvmpt.mm"
include "fveq2d.mm"
include "adantl.mm"
include "fvcoe1.mm"
include "adantlr.mm"
include "eqtr4d.mm"
include "imbi2d.mm"
include "ralbidva.mm"
include "syl5bbr.mm"
include "bitr4d.mm"

theorem deg1leb
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cD: class D
  let cP: class P
  let cR: class R
  let cF: class F
  let cG: class G
  let c.0: class .0.
  let vy: setvar y
  let vb: setvar b
  let va: setvar a
  assume deg1leb.d: |- D = ( deg1 ` R )
  assume deg1leb.p: |- P = ( Poly1 ` R )
  assume deg1leb.b: |- B = ( Base ` P )
  assume deg1leb.y: |- .0. = ( 0g ` R )
  assume deg1leb.a: |- A = ( coe1 ` F )

  disjoint A x
  disjoint G x
  disjoint .0. x
  disjoint A y
  disjoint x y
  disjoint B y
  disjoint F y
  disjoint G y
  disjoint R y
  disjoint .0. b
  disjoint .0. y
  disjoint b x
  disjoint b y
  disjoint a b
  assert |- ( ( F e. B /\ G e. RR* ) -> ( ( D ` F ) <_ G <-> A. x e. NN0 ( G < x -> ( A ` x ) = .0. ) ) )

  proof
    cF
    cB
    wcel
    #
    cG
    cxr
    wcel
    #
    wa
    #
    cF
    cD
    cfv
    cG
    cle
    wbr
    cG
    vy
    cv
    #
    vb
    cn0
    c1o
    cmap
    co
    #
    c0
    vb
    cv
    #
    cfv
    #
    cmpt
    #
    cfv
    #
    clt
    wbr
    #
    @3
    cF
    cfv
    #
    c.0
    wceq
    #
    wi
    #
    vy
    @4
    wral
    #
    cG
    vx
    cv
    #
    clt
    wbr
    #
    @14
    cA
    cfv
    #
    c.0
    wceq
    #
    wi
    #
    vx
    cn0
    wral
    #
    vy
    @4
    cB
    cD
    c1o
    cR
    cmpl
    co
    #
    cR
    vb
    va
    cF
    cG
    @7
    c1o
    c.0
    cD
    cR
    deg1leb.d
    deg1fval
    @20
    eqid
    cP
    cR
    cR
    cps1
    cfv
    #
    cB
    deg1leb.p
    @21
    eqid
    deg1leb.b
    ply1bas
    deg1leb.y
    va
    psr1baslem
    vb
    tdeglem2
    mdegleb
    @19
    @9
    @8
    cA
    cfv
    #
    c.0
    wceq
    #
    wi
    #
    vy
    @4
    wral
    #
    @2
    @13
    @4
    cn0
    @7
    wf1o
    @4
    cn0
    @7
    wfo
    @25
    @19
    wb
    vb
    cn0
    c1o
    @7
    c0
    df1o2
    nn0ex
    0ex
    @7
    eqid
    #
    mapsnf1o2
    @4
    cn0
    @7
    f1ofo
    @24
    @18
    vy
    vx
    @4
    cn0
    @7
    @8
    @14
    wceq
    #
    @9
    @15
    @23
    @17
    @8
    @14
    cG
    clt
    breq2
    @27
    @22
    @16
    c.0
    @8
    @14
    cA
    fveq2
    eqeq1d
    imbi12d
    cbvfo
    mp2b
    @2
    @24
    @12
    vy
    @4
    @2
    @3
    @4
    wcel
    #
    wa
    #
    @23
    @11
    @9
    @29
    @22
    @10
    c.0
    @29
    @22
    c0
    @3
    cfv
    #
    cA
    cfv
    #
    @10
    @28
    @22
    @31
    wceq
    @2
    @28
    @8
    @30
    cA
    vb
    @3
    @6
    @30
    @4
    @7
    c0
    @5
    @3
    fveq1
    @26
    c0
    @3
    fvex
    fvmpt
    fveq2d
    adantl
    @0
    @28
    @10
    @31
    wceq
    @1
    cA
    cF
    cB
    @3
    deg1leb.a
    fvcoe1
    adantlr
    eqtr4d
    eqeq1d
    imbi2d
    ralbidva
    syl5bbr
    bitr4d
end
