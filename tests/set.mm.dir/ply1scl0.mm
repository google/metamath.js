include "crg.mm"
include "wcel.mm"
include "cfv.mm"
include "cur.mm"
include "cvsca.mm"
include "co.mm"
include "cid.mm"
include "c0g.mm"
include "cbs.mm"
include "wceq.mm"
include "eqid.mm"
include "ring0cl.mm"
include "ply1sca2.mm"
include "c1.mm"
include "df-base.mm"
include "strfvi.mm"
include "asclval.mm"
include "syl.mm"
include "fvi.mm"
include "fveq2d.mm"
include "syl6reqr.mm"
include "oveq1d.mm"
include "clmod.mm"
include "ply1lmod.mm"
include "ply1ring.mm"
include "ringidcl.mm"
include "lmod0vs.mm"
include "syl2anc.mm"
include "3eqtrd.mm"

theorem ply1scl0
  let cA: class A
  let cP: class P
  let cR: class R
  let cY: class Y
  let c.0: class .0.
  let vx: setvar x
  let vy: setvar y
  let cK: class K
  let cX: class X
  assume ply1scl.p: |- P = ( Poly1 ` R )
  assume ply1scl.a: |- A = ( algSc ` P )
  assume ply1scl0.z: |- .0. = ( 0g ` R )
  assume ply1scl0.y: |- Y = ( 0g ` P )


  assert |- ( R e. Ring -> ( A ` .0. ) = Y )

  proof
    cR
    crg
    wcel
    #
    c.0
    cA
    cfv
    #
    c.0
    cP
    cur
    cfv
    #
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
    c0g
    cfv
    #
    @2
    @3
    co
    #
    cY
    @0
    c.0
    cR
    cbs
    cfv
    #
    wcel
    @1
    @4
    wceq
    @8
    cR
    c.0
    @8
    eqid
    #
    ply1scl0.z
    ring0cl
    cA
    @3
    @2
    @5
    @8
    cP
    c.0
    ply1scl.a
    cP
    cR
    ply1scl.p
    ply1sca2
    #
    cR
    cbs
    c1
    @8
    df-base
    @9
    strfvi
    @3
    eqid
    #
    @2
    eqid
    #
    asclval
    syl
    @0
    c.0
    @6
    @2
    @3
    @0
    @6
    cR
    c0g
    cfv
    c.0
    @0
    @5
    cR
    c0g
    cR
    crg
    fvi
    fveq2d
    ply1scl0.z
    syl6reqr
    oveq1d
    @0
    cP
    clmod
    wcel
    @2
    cP
    cbs
    cfv
    #
    wcel
    #
    @7
    cY
    wceq
    cP
    cR
    ply1scl.p
    ply1lmod
    @0
    cP
    crg
    wcel
    @14
    cP
    cR
    ply1scl.p
    ply1ring
    @13
    cP
    @2
    @13
    eqid
    #
    @12
    ringidcl
    syl
    @3
    @5
    @6
    @13
    cP
    @2
    cY
    @15
    @10
    @11
    @6
    eqid
    ply1scl0.y
    lmod0vs
    syl2anc
    3eqtrd
end
