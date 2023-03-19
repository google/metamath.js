include "ccrg.mm"
include "wcel.mm"
include "cfv.mm"
include "cascl.mm"
include "crg.mm"
include "wceq.mm"
include "crngring.mm"
include "eqid.mm"
include "ply1scl0.mm"
include "syl.mm"
include "eqcomd.mm"
include "fveq2d.mm"
include "fveq1d.mm"
include "cbs.mm"
include "id.mm"
include "cgrp.mm"
include "ringgrp.mm"
include "grpidcl.mm"
include "3syl.mm"
include "evl1scad.mm"
include "simprd.mm"
include "eqtrd.mm"

theorem evl1at0
  let cP: class P
  let cR: class R
  let cO: class O
  let c.0: class .0.
  let cZ: class Z
  let vk: setvar k
  let vx: setvar x
  assume evl1at0.o: |- O = ( eval1 ` R )
  assume evl1at0.p: |- P = ( Poly1 ` R )
  assume evl1at0.0: |- .0. = ( 0g ` R )
  assume evl1at0.z: |- Z = ( 0g ` P )


  assert |- ( R e. CRing -> ( ( O ` Z ) ` .0. ) = .0. )

  proof
    cR
    ccrg
    wcel
    #
    c.0
    cZ
    cO
    cfv
    #
    cfv
    c.0
    c.0
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
    c.0
    @0
    c.0
    @1
    @4
    @0
    cZ
    @3
    cO
    @0
    @3
    cZ
    @0
    cR
    crg
    wcel
    #
    @3
    cZ
    wceq
    cR
    crngring
    #
    @2
    cP
    cR
    cZ
    c.0
    evl1at0.p
    @2
    eqid
    #
    evl1at0.0
    evl1at0.z
    ply1scl0
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
    c.0
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
    c.0
    c.0
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
    cR
    cgrp
    wcel
    c.0
    @10
    wcel
    @7
    cR
    ringgrp
    @10
    cR
    c.0
    @11
    evl1at0.0
    grpidcl
    3syl
    #
    @12
    evl1scad
    simprd
    eqtrd
end
