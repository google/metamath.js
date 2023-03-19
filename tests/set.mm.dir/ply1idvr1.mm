include "crg.mm"
include "wcel.mm"
include "cc0.mm"
include "co.mm"
include "cur.mm"
include "cfv.mm"
include "cascl.mm"
include "cvsca.mm"
include "csca.mm"
include "cbs.mm"
include "wceq.mm"
include "eqid.mm"
include "ringidcl.mm"
include "ply1scltm.mm"
include "mpdan.mm"
include "ply1sca.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "clmod.mm"
include "ply1lmod.mm"
include "cn0.mm"
include "0nn0.mm"
include "ply1moncl.mm"
include "mpan2.mm"
include "lmodvs1.mm"
include "syl2anc.mm"
include "3eqtrrd.mm"
include "ply1scl1.mm"
include "eqtrd.mm"

theorem ply1idvr1
  let cP: class P
  let cR: class R
  let c.ex: class .^
  let cN: class N
  let cX: class X
  assume ply1idvr1.p: |- P = ( Poly1 ` R )
  assume ply1idvr1.x: |- X = ( var1 ` R )
  assume ply1idvr1.n: |- N = ( mulGrp ` P )
  assume ply1idvr1.e: |- .^ = ( .g ` N )


  assert |- ( R e. Ring -> ( 0 .^ X ) = ( 1r ` P ) )

  proof
    cR
    crg
    wcel
    #
    cc0
    cX
    c.ex
    co
    #
    cR
    cur
    cfv
    #
    cP
    cascl
    cfv
    #
    cfv
    #
    cP
    cur
    cfv
    #
    @0
    @4
    @2
    @1
    cP
    cvsca
    cfv
    #
    co
    #
    cP
    csca
    cfv
    #
    cur
    cfv
    #
    @1
    @6
    co
    #
    @1
    @0
    @2
    cR
    cbs
    cfv
    #
    wcel
    @4
    @7
    wceq
    @11
    cR
    @2
    @11
    eqid
    #
    @2
    eqid
    #
    ringidcl
    @3
    cP
    cR
    @6
    c.ex
    @2
    @11
    cN
    cX
    @12
    ply1idvr1.p
    ply1idvr1.x
    @6
    eqid
    #
    ply1idvr1.n
    ply1idvr1.e
    @3
    eqid
    #
    ply1scltm
    mpdan
    @0
    @2
    @9
    @1
    @6
    @0
    cR
    @8
    cur
    cP
    cR
    crg
    ply1idvr1.p
    ply1sca
    fveq2d
    oveq1d
    @0
    cP
    clmod
    wcel
    @1
    cP
    cbs
    cfv
    #
    wcel
    #
    @10
    @1
    wceq
    cP
    cR
    ply1idvr1.p
    ply1lmod
    @0
    cc0
    cn0
    wcel
    @17
    0nn0
    @16
    cc0
    cP
    cR
    c.ex
    cN
    cX
    ply1idvr1.p
    ply1idvr1.x
    ply1idvr1.n
    ply1idvr1.e
    @16
    eqid
    #
    ply1moncl
    mpan2
    @6
    @9
    @8
    @16
    cP
    @1
    @18
    @8
    eqid
    @14
    @9
    eqid
    lmodvs1
    syl2anc
    3eqtrrd
    @3
    cP
    cR
    @2
    @5
    ply1idvr1.p
    @15
    @13
    @5
    eqid
    ply1scl1
    eqtrd
end
