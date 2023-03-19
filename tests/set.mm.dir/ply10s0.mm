include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "co.mm"
include "csca.mm"
include "cfv.mm"
include "c0g.mm"
include "wceq.mm"
include "ply1sca.mm"
include "adantr.mm"
include "fveq2d.mm"
include "syl5eq.mm"
include "oveq1d.mm"
include "clmod.mm"
include "ply1lmod.mm"
include "eqid.mm"
include "lmod0vs.mm"
include "sylan.mm"
include "eqtrd.mm"

theorem ply10s0
  let cB: class B
  let cP: class P
  let cR: class R
  let c.as: class .*
  let cM: class M
  let c.0: class .0.
  assume ply10s0.p: |- P = ( Poly1 ` R )
  assume ply10s0.b: |- B = ( Base ` P )
  assume ply10s0.m: |- .* = ( .s ` P )
  assume ply10s0.e: |- .0. = ( 0g ` R )


  assert |- ( ( R e. Ring /\ M e. B ) -> ( .0. .* M ) = ( 0g ` P ) )

  proof
    cR
    crg
    wcel
    #
    cM
    cB
    wcel
    #
    wa
    #
    c.0
    cM
    c.as
    co
    cP
    csca
    cfv
    #
    c0g
    cfv
    #
    cM
    c.as
    co
    #
    cP
    c0g
    cfv
    #
    @2
    c.0
    @4
    cM
    c.as
    @2
    c.0
    cR
    c0g
    cfv
    @4
    ply10s0.e
    @2
    cR
    @3
    c0g
    @0
    cR
    @3
    wceq
    @1
    cP
    cR
    crg
    ply10s0.p
    ply1sca
    adantr
    fveq2d
    syl5eq
    oveq1d
    @0
    cP
    clmod
    wcel
    @1
    @5
    @6
    wceq
    cP
    cR
    ply10s0.p
    ply1lmod
    c.as
    @3
    @4
    cB
    cP
    cM
    @6
    ply10s0.b
    @3
    eqid
    ply10s0.m
    @4
    eqid
    @6
    eqid
    lmod0vs
    sylan
    eqtrd
end
