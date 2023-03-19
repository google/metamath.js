include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cur.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "cid.mm"
include "ply1sca2.mm"
include "cbs.mm"
include "c1.mm"
include "df-base.mm"
include "strfvi.mm"
include "eqid.mm"
include "asclval.mm"
include "adantl.mm"
include "vr1cl.mm"
include "mgpbas.mm"
include "ringidval.mm"
include "mulg0.mm"
include "syl.mm"
include "adantr.mm"
include "oveq2d.mm"
include "eqtr4d.mm"

theorem ply1scltm
  let cA: class A
  let cP: class P
  let cR: class R
  let c.x: class .x.
  let c.ex: class .^
  let cF: class F
  let cK: class K
  let cN: class N
  let cX: class X
  assume ply1scltm.k: |- K = ( Base ` R )
  assume ply1scltm.p: |- P = ( Poly1 ` R )
  assume ply1scltm.x: |- X = ( var1 ` R )
  assume ply1scltm.m: |- .x. = ( .s ` P )
  assume ply1scltm.n: |- N = ( mulGrp ` P )
  assume ply1scltm.e: |- .^ = ( .g ` N )
  assume ply1scltm.a: |- A = ( algSc ` P )


  assert |- ( ( R e. Ring /\ F e. K ) -> ( A ` F ) = ( F .x. ( 0 .^ X ) ) )

  proof
    cR
    crg
    wcel
    #
    cF
    cK
    wcel
    #
    wa
    #
    cF
    cA
    cfv
    #
    cF
    cP
    cur
    cfv
    #
    c.x
    co
    #
    cF
    cc0
    cX
    c.ex
    co
    #
    c.x
    co
    @1
    @3
    @5
    wceq
    @0
    cA
    c.x
    @4
    cR
    cid
    cfv
    cK
    cP
    cF
    ply1scltm.a
    cP
    cR
    ply1scltm.p
    ply1sca2
    cR
    cbs
    c1
    cK
    df-base
    ply1scltm.k
    strfvi
    ply1scltm.m
    @4
    eqid
    #
    asclval
    adantl
    @2
    @6
    @4
    cF
    c.x
    @0
    @6
    @4
    wceq
    #
    @1
    @0
    cX
    cP
    cbs
    cfv
    #
    wcel
    @8
    @9
    cP
    cR
    cX
    ply1scltm.x
    ply1scltm.p
    @9
    eqid
    #
    vr1cl
    @9
    c.ex
    cN
    cX
    @4
    @9
    cP
    cN
    ply1scltm.n
    @10
    mgpbas
    cP
    @4
    cN
    ply1scltm.n
    @7
    ringidval
    ply1scltm.e
    mulg0
    syl
    adantr
    oveq2d
    eqtr4d
end
