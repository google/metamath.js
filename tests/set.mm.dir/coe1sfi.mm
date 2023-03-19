include "wcel.mm"
include "cn0.mm"
include "c1o.mm"
include "cmap.mm"
include "co.mm"
include "c0.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "ccnv.mm"
include "ccom.mm"
include "cfsupp.mm"
include "df1o2.mm"
include "nn0ex.mm"
include "0ex.mm"
include "eqid.mm"
include "mapsncnv.mm"
include "coe1fval2.mm"
include "cvv.mm"
include "cmpl.mm"
include "cbs.mm"
include "ply1bascl2.mm"
include "cpl1.mm"
include "elbasfv.mm"
include "mplelsfi.mm"
include "wf1.mm"
include "wf1o.mm"
include "mapsnf1o2.mm"
include "f1ocnv.mm"
include "f1of1.mm"
include "mp2b.mm"
include "a1i.mm"
include "c0g.mm"
include "fvex.mm"
include "eqeltri.mm"
include "id.mm"
include "fsuppco.mm"
include "eqbrtrd.mm"

theorem coe1sfi
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let cF: class F
  let c.0: class .0.
  let vy: setvar y
  let vx: setvar x
  assume coe1sfi.a: |- A = ( coe1 ` F )
  assume coe1sfi.b: |- B = ( Base ` P )
  assume coe1sfi.p: |- P = ( Poly1 ` R )
  assume coe1sfi.z: |- .0. = ( 0g ` R )


  assert |- ( F e. B -> A finSupp .0. )

  proof
    cF
    cB
    wcel
    #
    cA
    cF
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
    ccnv
    #
    ccom
    c.0
    cfsupp
    vy
    cA
    cB
    cP
    cR
    cF
    @3
    coe1sfi.a
    coe1sfi.b
    coe1sfi.p
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
    #
    mapsncnv
    coe1fval2
    @0
    cF
    @3
    cB
    cvv
    cn0
    @1
    c.0
    @0
    c1o
    cR
    cmpl
    co
    #
    cbs
    cfv
    #
    @5
    cR
    cF
    c1o
    cvv
    c.0
    @5
    eqid
    @6
    eqid
    coe1sfi.z
    cB
    cP
    cR
    cF
    coe1sfi.p
    coe1sfi.b
    ply1bascl2
    cB
    cP
    cpl1
    cF
    cR
    coe1sfi.p
    coe1sfi.b
    elbasfv
    mplelsfi
    cn0
    @1
    @3
    wf1
    #
    @0
    @1
    cn0
    @2
    wf1o
    cn0
    @1
    @3
    wf1o
    @7
    vx
    cn0
    c1o
    @2
    c0
    df1o2
    nn0ex
    0ex
    @4
    mapsnf1o2
    @1
    cn0
    @2
    f1ocnv
    cn0
    @1
    @3
    f1of1
    mp2b
    a1i
    c.0
    cvv
    wcel
    @0
    c.0
    cR
    c0g
    cfv
    cvv
    coe1sfi.z
    cR
    c0g
    fvex
    eqeltri
    a1i
    @0
    id
    fsuppco
    eqbrtrd
end
