include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "csca.mm"
include "cfv.mm"
include "cvv.mm"
include "cn0.mm"
include "cbs.mm"
include "cv.mm"
include "co.mm"
include "eqid.mm"
include "clmod.mm"
include "ply1lmod.mm"
include "adantr.mm"
include "nn0ex.mm"
include "a1i.mm"
include "cmnd.mm"
include "ply1ring.mm"
include "ringmgp.mm"
include "syl.mm"
include "ad2antrr.mm"
include "simpr.mm"
include "vr1cl.mm"
include "mgpbas.mm"
include "mulgnn0cl.mm"
include "syl3anc.mm"
include "wf.mm"
include "coe1f.mm"
include "adantl.mm"
include "c0g.mm"
include "cfsupp.mm"
include "wbr.mm"
include "coe1sfi.mm"
include "wceq.mm"
include "ply1sca.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "breqtrrd.mm"
include "mptscmfsuppd.mm"

theorem ply1coefsupp
  let cA: class A
  let cB: class B
  let cP: class P
  let cR: class R
  let c.x: class .x.
  let vk: setvar k
  let c.ex: class .^
  let cK: class K
  let cM: class M
  let cX: class X
  assume ply1coefsupp.p: |- P = ( Poly1 ` R )
  assume ply1coefsupp.x: |- X = ( var1 ` R )
  assume ply1coefsupp.b: |- B = ( Base ` P )
  assume ply1coefsupp.n: |- .x. = ( .s ` P )
  assume ply1coefsupp.m: |- M = ( mulGrp ` P )
  assume ply1coefsupp.e: |- .^ = ( .g ` M )
  assume ply1coefsupp.a: |- A = ( coe1 ` K )

  disjoint A k
  disjoint B k
  disjoint K k
  disjoint P k
  disjoint R k
  disjoint .x. k
  assert |- ( ( R e. Ring /\ K e. B ) -> ( k e. NN0 |-> ( ( A ` k ) .x. ( k .^ X ) ) ) finSupp ( 0g ` P ) )

  proof
    cR
    crg
    wcel
    #
    cK
    cB
    wcel
    #
    wa
    #
    cA
    cB
    cP
    cP
    csca
    cfv
    #
    c.x
    vk
    cvv
    cn0
    cR
    cbs
    cfv
    #
    vk
    cv
    #
    cX
    c.ex
    co
    #
    ply1coefsupp.b
    @3
    eqid
    ply1coefsupp.n
    @0
    cP
    clmod
    wcel
    @1
    cP
    cR
    ply1coefsupp.p
    ply1lmod
    adantr
    cn0
    cvv
    wcel
    @2
    nn0ex
    a1i
    @2
    @5
    cn0
    wcel
    #
    wa
    cM
    cmnd
    wcel
    #
    @7
    cX
    cB
    wcel
    #
    @6
    cB
    wcel
    @0
    @8
    @1
    @7
    @0
    cP
    crg
    wcel
    @8
    cP
    cR
    ply1coefsupp.p
    ply1ring
    cP
    cM
    ply1coefsupp.m
    ringmgp
    syl
    ad2antrr
    @2
    @7
    simpr
    @0
    @9
    @1
    @7
    cB
    cP
    cR
    cX
    ply1coefsupp.x
    ply1coefsupp.p
    ply1coefsupp.b
    vr1cl
    ad2antrr
    cB
    c.ex
    cM
    @5
    cX
    cB
    cP
    cM
    ply1coefsupp.m
    ply1coefsupp.b
    mgpbas
    ply1coefsupp.e
    mulgnn0cl
    syl3anc
    @1
    cn0
    @4
    cA
    wf
    @0
    cA
    cB
    cP
    cR
    cK
    @4
    ply1coefsupp.a
    ply1coefsupp.b
    ply1coefsupp.p
    @4
    eqid
    coe1f
    adantl
    @2
    cA
    cR
    c0g
    cfv
    #
    @3
    c0g
    cfv
    cfsupp
    @1
    cA
    @10
    cfsupp
    wbr
    @0
    cA
    cB
    cP
    cR
    cK
    @10
    ply1coefsupp.a
    ply1coefsupp.b
    ply1coefsupp.p
    @10
    eqid
    coe1sfi
    adantl
    @2
    @3
    cR
    c0g
    @0
    @3
    cR
    wceq
    @1
    @0
    cR
    @3
    cP
    cR
    crg
    ply1coefsupp.p
    ply1sca
    eqcomd
    adantr
    fveq2d
    breqtrrd
    mptscmfsuppd
end
