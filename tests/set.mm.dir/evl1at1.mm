include "ccrg.mm"
include "wcel.mm"
include "cfv.mm"
include "cascl.mm"
include "crg.mm"
include "wceq.mm"
include "crngring.mm"
include "eqid.mm"
include "ply1scl1.mm"
include "syl.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "fveq1d.mm"
include "cbs.mm"
include "id.mm"
include "ringidcl.mm"
include "evl1scad.mm"
include "simprd.mm"
include "eqtrd.mm"

theorem evl1at1
  let cP: class P
  let cR: class R
  let c.1: class .1.
  let cI: class I
  let cO: class O
  let vk: setvar k
  let vx: setvar x
  assume evl1at0.o: |- O = ( eval1 ` R )
  assume evl1at0.p: |- P = ( Poly1 ` R )
  assume evl1at1.1: |- .1. = ( 1r ` R )
  assume evl1at1.i: |- I = ( 1r ` P )


  assert |- ( R e. CRing -> ( ( O ` I ) ` .1. ) = .1. )

  proof
    cR
    ccrg
    wcel
    #
    c.1
    cI
    cO
    cfv
    #
    cfv
    c.1
    c.1
    cP
    cascl
    cfv
    #
    cfv
    #
    cO
    cfv
    #
    cfv
    #
    c.1
    @0
    c.1
    @1
    @4
    @0
    cI
    @3
    cO
    @0
    @3
    cI
    @0
    cR
    crg
    wcel
    #
    @3
    cI
    wceq
    cR
    crngring
    #
    @2
    cP
    cR
    c.1
    cI
    evl1at0.p
    @2
    eqid
    #
    evl1at1.1
    evl1at1.i
    ply1scl1
    syl
    eqcomd
    fveq2d
    fveq1d
    @0
    @3
    cP
    cbs
    cfv
    #
    wcel
    @5
    c.1
    wceq
    @0
    @2
    cR
    cbs
    cfv
    #
    cP
    cR
    @9
    cO
    c.1
    c.1
    evl1at0.o
    evl1at0.p
    @10
    eqid
    #
    @8
    @9
    eqid
    @0
    id
    @0
    @6
    c.1
    @10
    wcel
    @7
    @10
    cR
    c.1
    @11
    evl1at1.1
    ringidcl
    syl
    #
    @12
    evl1scad
    simprd
    eqtrd
end
