include "wcel.mm"
include "cfv.mm"
include "cn0.mm"
include "c1o.mm"
include "cmap.mm"
include "co.mm"
include "c0.mm"
include "cv.mm"
include "cmpt.mm"
include "csupp.mm"
include "cima.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "cmpl.mm"
include "deg1fval.mm"
include "eqid.mm"
include "cps1.mm"
include "ply1bas.mm"
include "psr1baslem.mm"
include "tdeglem2.mm"
include "mdegval.mm"
include "ccnv.mm"
include "cvv.mm"
include "csn.mm"
include "cdif.mm"
include "ccom.mm"
include "wceq.mm"
include "c0g.mm"
include "fvex.mm"
include "eqeltri.mm"
include "suppimacnv.mm"
include "mpan2.mm"
include "imaeq2d.mm"
include "imaco.mm"
include "syl6eqr.mm"
include "df1o2.mm"
include "nn0ex.mm"
include "0ex.mm"
include "mapsncnv.mm"
include "coe1fval2.mm"
include "cnveqd.mm"
include "cnvco.mm"
include "cocnvcnv1.mm"
include "eqtri.mm"
include "syl6req.mm"
include "imaeq1d.mm"
include "eqtrd.mm"
include "cco1.mm"
include "wa.mm"
include "eqcomd.mm"
include "mp2an.mm"
include "syl6eq.mm"
include "supeq1d.mm"

theorem deg1val
  let cA: class A
  let cB: class B
  let cD: class D
  let cP: class P
  let cR: class R
  let cF: class F
  let c.0: class .0.
  let vx: setvar x
  let vy: setvar y
  let cG: class G
  let vb: setvar b
  let va: setvar a
  assume deg1leb.d: |- D = ( deg1 ` R )
  assume deg1leb.p: |- P = ( Poly1 ` R )
  assume deg1leb.b: |- B = ( Base ` P )
  assume deg1leb.y: |- .0. = ( 0g ` R )
  assume deg1leb.a: |- A = ( coe1 ` F )


  assert |- ( F e. B -> ( D ` F ) = sup ( ( A supp .0. ) , RR* , < ) )

  proof
    cF
    cB
    wcel
    #
    cF
    cD
    cfv
    vx
    cn0
    c1o
    cmap
    co
    #
    c0
    vx
    cv
    cfv
    cmpt
    #
    cF
    c.0
    csupp
    co
    #
    cima
    #
    cxr
    clt
    csup
    cA
    c.0
    csupp
    co
    #
    cxr
    clt
    csup
    @1
    cB
    cD
    c1o
    cR
    cmpl
    co
    #
    cR
    vx
    vy
    cF
    @2
    c1o
    c.0
    cD
    cR
    deg1leb.d
    deg1fval
    @6
    eqid
    cP
    cR
    cR
    cps1
    cfv
    #
    cB
    deg1leb.p
    @7
    eqid
    deg1leb.b
    ply1bas
    deg1leb.y
    vy
    psr1baslem
    vx
    tdeglem2
    mdegval
    @0
    cxr
    @4
    @5
    clt
    @0
    @4
    cA
    ccnv
    #
    cvv
    c.0
    csn
    cdif
    #
    cima
    #
    @5
    @0
    @4
    @2
    cF
    ccnv
    #
    ccom
    #
    @9
    cima
    #
    @10
    @0
    @4
    @2
    @11
    @9
    cima
    #
    cima
    @13
    @0
    @3
    @14
    @2
    @0
    c.0
    cvv
    wcel
    #
    @3
    @14
    wceq
    c.0
    cR
    c0g
    cfv
    cvv
    deg1leb.y
    cR
    c0g
    fvex
    eqeltri
    #
    cF
    cB
    cvv
    c.0
    suppimacnv
    mpan2
    imaeq2d
    @2
    @11
    @9
    imaco
    syl6eqr
    @0
    @12
    @8
    @9
    @0
    @8
    cF
    @2
    ccnv
    #
    ccom
    #
    ccnv
    #
    @12
    @0
    cA
    @18
    vy
    cA
    cB
    cP
    cR
    cF
    @17
    deg1leb.a
    deg1leb.b
    deg1leb.p
    vx
    vy
    cn0
    c1o
    @2
    c0
    df1o2
    nn0ex
    0ex
    @2
    eqid
    mapsncnv
    coe1fval2
    cnveqd
    @19
    @17
    ccnv
    @11
    ccom
    @12
    cF
    @17
    cnvco
    @2
    @11
    cocnvcnv1
    eqtri
    syl6req
    imaeq1d
    eqtrd
    cA
    cvv
    wcel
    #
    @15
    @10
    @5
    wceq
    cA
    cF
    cco1
    cfv
    cvv
    deg1leb.a
    cF
    cco1
    fvex
    eqeltri
    @16
    @20
    @15
    wa
    @5
    @10
    cA
    cvv
    cvv
    c.0
    suppimacnv
    eqcomd
    mp2an
    syl6eq
    supeq1d
    eqtrd
end
