include "cgrp.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "cn0.mm"
include "co.mm"
include "wceq.mm"
include "cneg.mm"
include "cmnd.mm"
include "grpmnd.mm"
include "adantr.mm"
include "mulgnn0z.mm"
include "sylan.mm"
include "cminusg.mm"
include "cfv.mm"
include "simpll.mm"
include "nn0z.mm"
include "adantl.mm"
include "grpidcl.mm"
include "ad2antrr.mm"
include "eqid.mm"
include "mulgneg.mm"
include "syl3anc.mm"
include "cc.mm"
include "zcn.mm"
include "ad2antlr.mm"
include "negnegd.mm"
include "oveq1d.mm"
include "fveq2d.mm"
include "grpinvid.mm"
include "eqtrd.mm"
include "3eqtr3d.mm"
include "wo.mm"
include "cr.mm"
include "elznn0.mm"
include "simprbi.mm"
include "mpjaodan.mm"

theorem mulgz
  let cB: class B
  let c.x: class .x.
  let cG: class G
  let cN: class N
  let c.0: class .0.
  let vx: setvar x
  assume mulgnn0z.b: |- B = ( Base ` G )
  assume mulgnn0z.t: |- .x. = ( .g ` G )
  assume mulgnn0z.o: |- .0. = ( 0g ` G )


  assert |- ( ( G e. Grp /\ N e. ZZ ) -> ( N .x. .0. ) = .0. )

  proof
    cG
    cgrp
    wcel
    #
    cN
    cz
    wcel
    #
    wa
    #
    cN
    cn0
    wcel
    #
    cN
    c.0
    c.x
    co
    #
    c.0
    wceq
    #
    cN
    cneg
    #
    cn0
    wcel
    #
    @2
    cG
    cmnd
    wcel
    #
    @3
    @5
    @0
    @8
    @1
    cG
    grpmnd
    adantr
    #
    cB
    c.x
    cG
    cN
    c.0
    mulgnn0z.b
    mulgnn0z.t
    mulgnn0z.o
    mulgnn0z
    sylan
    @2
    @7
    wa
    #
    @6
    cneg
    #
    c.0
    c.x
    co
    #
    @6
    c.0
    c.x
    co
    #
    cG
    cminusg
    cfv
    #
    cfv
    #
    @4
    c.0
    @10
    @0
    @6
    cz
    wcel
    #
    c.0
    cB
    wcel
    #
    @12
    @15
    wceq
    @0
    @1
    @7
    simpll
    @7
    @16
    @2
    @6
    nn0z
    adantl
    @0
    @17
    @1
    @7
    cB
    cG
    c.0
    mulgnn0z.b
    mulgnn0z.o
    grpidcl
    ad2antrr
    cB
    c.x
    cG
    @14
    @6
    c.0
    mulgnn0z.b
    mulgnn0z.t
    @14
    eqid
    #
    mulgneg
    syl3anc
    @10
    @11
    cN
    c.0
    c.x
    @10
    cN
    @1
    cN
    cc
    wcel
    @0
    @7
    cN
    zcn
    ad2antlr
    negnegd
    oveq1d
    @10
    @15
    c.0
    @14
    cfv
    #
    c.0
    @10
    @13
    c.0
    @14
    @2
    @8
    @7
    @13
    c.0
    wceq
    @9
    cB
    c.x
    cG
    @6
    c.0
    mulgnn0z.b
    mulgnn0z.t
    mulgnn0z.o
    mulgnn0z
    sylan
    fveq2d
    @0
    @19
    c.0
    wceq
    @1
    @7
    cG
    @14
    c.0
    mulgnn0z.o
    @18
    grpinvid
    ad2antrr
    eqtrd
    3eqtr3d
    @1
    @3
    @7
    wo
    #
    @0
    @1
    cN
    cr
    wcel
    @20
    cN
    elznn0
    simprbi
    adantl
    mpjaodan
end
