include "crg.mm"
include "wcel.mm"
include "w3a.mm"
include "cfv.mm"
include "co.mm"
include "cur.mm"
include "wceq.mm"
include "wa.mm"
include "csca.mm"
include "cbs.mm"
include "ply1sca.mm"
include "fveq2d.mm"
include "syl5eq.mm"
include "eleq2d.mm"
include "biimpa.mm"
include "eqid.mm"
include "asclval.mm"
include "syl.mm"
include "3adant3.mm"
include "oveq1d.mm"
include "simp1.mm"
include "eleq2i.mm"
include "biimpi.mm"
include "3ad2ant2.mm"
include "ply1ring.mm"
include "ringidcl.mm"
include "3ad2ant1.mm"
include "simp3.mm"
include "ply1ass23l.mm"
include "syl13anc.mm"
include "ringlidm.mm"
include "sylan.mm"
include "3adant2.mm"
include "oveq2d.mm"
include "3eqtrd.mm"

theorem ply1sclrmsm
  let cA: class A
  let cP: class P
  let cR: class R
  let c.x: class .x.
  let c.xp: class .X.
  let cE: class E
  let c.ex: class .^
  let cF: class F
  let cK: class K
  let cN: class N
  let cX: class X
  let cZ: class Z
  let vk: setvar k
  let vx: setvar x
  assume ply1sclrmsm.k: |- K = ( Base ` R )
  assume ply1sclrmsm.p: |- P = ( Poly1 ` R )
  assume ply1sclrmsm.b: |- E = ( Base ` P )
  assume ply1sclrmsm.x: |- X = ( var1 ` R )
  assume ply1sclrmsm.s: |- .x. = ( .s ` P )
  assume ply1sclrmsm.m: |- .X. = ( .r ` P )
  assume ply1sclrmsm.n: |- N = ( mulGrp ` P )
  assume ply1sclrmsm.e: |- .^ = ( .g ` N )
  assume ply1sclrmsm.a: |- A = ( algSc ` P )


  assert |- ( ( R e. Ring /\ F e. K /\ Z e. E ) -> ( ( A ` F ) .X. Z ) = ( F .x. Z ) )

  proof
    cR
    crg
    wcel
    #
    cF
    cK
    wcel
    #
    cZ
    cE
    wcel
    #
    w3a
    #
    cF
    cA
    cfv
    #
    cZ
    c.xp
    co
    cF
    cP
    cur
    cfv
    #
    c.x
    co
    #
    cZ
    c.xp
    co
    #
    cF
    @5
    cZ
    c.xp
    co
    #
    c.x
    co
    #
    cF
    cZ
    c.x
    co
    @3
    @4
    @6
    cZ
    c.xp
    @0
    @1
    @4
    @6
    wceq
    #
    @2
    @0
    @1
    wa
    cF
    cP
    csca
    cfv
    #
    cbs
    cfv
    #
    wcel
    #
    @10
    @0
    @1
    @13
    @0
    cK
    @12
    cF
    @0
    cK
    cR
    cbs
    cfv
    #
    @12
    ply1sclrmsm.k
    @0
    cR
    @11
    cbs
    cP
    cR
    crg
    ply1sclrmsm.p
    ply1sca
    fveq2d
    syl5eq
    eleq2d
    biimpa
    cA
    c.x
    @5
    @11
    @12
    cP
    cF
    ply1sclrmsm.a
    @11
    eqid
    @12
    eqid
    ply1sclrmsm.s
    @5
    eqid
    #
    asclval
    syl
    3adant3
    oveq1d
    @3
    @0
    cF
    @14
    wcel
    #
    @5
    cE
    wcel
    #
    @2
    @7
    @9
    wceq
    @0
    @1
    @2
    simp1
    @1
    @0
    @16
    @2
    @1
    @16
    cK
    @14
    cF
    ply1sclrmsm.k
    eleq2i
    biimpi
    3ad2ant2
    @0
    @1
    @17
    @2
    @0
    cP
    crg
    wcel
    #
    @17
    cP
    cR
    ply1sclrmsm.p
    ply1ring
    #
    cE
    cP
    @5
    ply1sclrmsm.b
    @15
    ringidcl
    syl
    3ad2ant1
    @0
    @1
    @2
    simp3
    cF
    cE
    cP
    cR
    c.x
    c.xp
    @14
    @5
    cZ
    ply1sclrmsm.p
    ply1sclrmsm.m
    ply1sclrmsm.b
    @14
    eqid
    ply1sclrmsm.s
    ply1ass23l
    syl13anc
    @3
    @8
    cZ
    cF
    c.x
    @0
    @2
    @8
    cZ
    wceq
    #
    @1
    @0
    @18
    @2
    @20
    @19
    cE
    cP
    c.xp
    @5
    cZ
    ply1sclrmsm.b
    ply1sclrmsm.m
    @15
    ringlidm
    sylan
    3adant2
    oveq2d
    3eqtrd
end
