include "crg.mm"
include "wcel.mm"
include "c1.mm"
include "co.mm"
include "csca.mm"
include "cfv.mm"
include "cur.mm"
include "ply1sca.mm"
include "fveq2d.mm"
include "syl5eq.mm"
include "oveq1d.mm"
include "clmod.mm"
include "cbs.mm"
include "wceq.mm"
include "ply1lmod.mm"
include "eqid.mm"
include "vr1cl.mm"
include "mgpbas.mm"
include "mulg1.mm"
include "syl.mm"
include "eqeltrd.mm"
include "lmodvs1.mm"
include "syl2anc.mm"
include "3eqtrd.mm"

theorem ply1vr1smo
  let cP: class P
  let cR: class R
  let c.x: class .x.
  let c.1: class .1.
  let c.ex: class .^
  let cG: class G
  let cX: class X
  let vk: setvar k
  let vx: setvar x
  assume ply1vr1smo.p: |- P = ( Poly1 ` R )
  assume ply1vr1smo.i: |- .1. = ( 1r ` R )
  assume ply1vr1smo.t: |- .x. = ( .s ` P )
  assume ply1vr1smo.m: |- G = ( mulGrp ` P )
  assume ply1vr1smo.e: |- .^ = ( .g ` G )
  assume ply1vr1smo.x: |- X = ( var1 ` R )


  assert |- ( R e. Ring -> ( .1. .x. ( 1 .^ X ) ) = X )

  proof
    cR
    crg
    wcel
    #
    c.1
    c1
    cX
    c.ex
    co
    #
    c.x
    co
    cP
    csca
    cfv
    #
    cur
    cfv
    #
    @1
    c.x
    co
    #
    @1
    cX
    @0
    c.1
    @3
    @1
    c.x
    @0
    c.1
    cR
    cur
    cfv
    @3
    ply1vr1smo.i
    @0
    cR
    @2
    cur
    cP
    cR
    crg
    ply1vr1smo.p
    ply1sca
    fveq2d
    syl5eq
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
    @4
    @1
    wceq
    cP
    cR
    ply1vr1smo.p
    ply1lmod
    @0
    @1
    cX
    @5
    @0
    cX
    @5
    wcel
    @1
    cX
    wceq
    @5
    cP
    cR
    cX
    ply1vr1smo.x
    ply1vr1smo.p
    @5
    eqid
    #
    vr1cl
    #
    @5
    c.ex
    cG
    cX
    @5
    cP
    cG
    ply1vr1smo.m
    @6
    mgpbas
    ply1vr1smo.e
    mulg1
    syl
    #
    @7
    eqeltrd
    c.x
    @3
    @2
    @5
    cP
    @1
    @6
    @2
    eqid
    ply1vr1smo.t
    @3
    eqid
    lmodvs1
    syl2anc
    @8
    3eqtrd
end
