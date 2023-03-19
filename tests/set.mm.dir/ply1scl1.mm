include "crg.mm"
include "wcel.mm"
include "cfv.mm"
include "cvsca.mm"
include "co.mm"
include "cid.mm"
include "cur.mm"
include "cbs.mm"
include "wceq.mm"
include "eqid.mm"
include "ringidcl.mm"
include "ply1sca2.mm"
include "c1.mm"
include "df-base.mm"
include "strfvi.mm"
include "asclval.mm"
include "syl.mm"
include "fvi.mm"
include "fveq2d.mm"
include "syl6eqr.mm"
include "oveq1d.mm"
include "clmod.mm"
include "ply1lmod.mm"
include "ply1ring.mm"
include "lmodvs1.mm"
include "syl2anc.mm"
include "3eqtr2d.mm"

theorem ply1scl1
  let cA: class A
  let cP: class P
  let cR: class R
  let c.1: class .1.
  let cN: class N
  let vx: setvar x
  let vy: setvar y
  let cK: class K
  let cX: class X
  let c.0: class .0.
  assume ply1scl.p: |- P = ( Poly1 ` R )
  assume ply1scl.a: |- A = ( algSc ` P )
  assume ply1scl1.o: |- .1. = ( 1r ` R )
  assume ply1scl1.n: |- N = ( 1r ` P )


  assert |- ( R e. Ring -> ( A ` .1. ) = N )

  proof
    cR
    crg
    wcel
    #
    c.1
    cA
    cfv
    #
    c.1
    cN
    cP
    cvsca
    cfv
    #
    co
    #
    cR
    cid
    cfv
    #
    cur
    cfv
    #
    cN
    @2
    co
    #
    cN
    @0
    c.1
    cR
    cbs
    cfv
    #
    wcel
    @1
    @3
    wceq
    @7
    cR
    c.1
    @7
    eqid
    #
    ply1scl1.o
    ringidcl
    cA
    @2
    cN
    @4
    @7
    cP
    c.1
    ply1scl.a
    cP
    cR
    ply1scl.p
    ply1sca2
    #
    cR
    cbs
    c1
    @7
    df-base
    @8
    strfvi
    @2
    eqid
    #
    ply1scl1.n
    asclval
    syl
    @0
    @5
    c.1
    cN
    @2
    @0
    @5
    cR
    cur
    cfv
    c.1
    @0
    @4
    cR
    cur
    cR
    crg
    fvi
    fveq2d
    ply1scl1.o
    syl6eqr
    oveq1d
    @0
    cP
    clmod
    wcel
    cN
    cP
    cbs
    cfv
    #
    wcel
    #
    @6
    cN
    wceq
    cP
    cR
    ply1scl.p
    ply1lmod
    @0
    cP
    crg
    wcel
    @12
    cP
    cR
    ply1scl.p
    ply1ring
    @11
    cP
    cN
    @11
    eqid
    #
    ply1scl1.n
    ringidcl
    syl
    @2
    @5
    @4
    @11
    cP
    cN
    @13
    @9
    @10
    @5
    eqid
    lmodvs1
    syl2anc
    3eqtr2d
end
