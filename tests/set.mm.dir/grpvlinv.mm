include "cgrp.mm"
include "wcel.mm"
include "cmap.mm"
include "co.mm"
include "wa.mm"
include "ccom.mm"
include "cvv.mm"
include "elmapex.mm"
include "simprd.mm"
include "adantl.mm"
include "wf.mm"
include "elmapi.mm"
include "grpidcl.mm"
include "adantr.mm"
include "grpinvf.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "wceq.mm"
include "fcompt.mm"
include "syl2an.mm"
include "grplinv.mm"
include "adantlr.mm"
include "caofinvl.mm"

theorem grpvlinv
  let cB: class B
  let c.pl: class .+
  let cG: class G
  let cI: class I
  let cN: class N
  let cX: class X
  let c.0: class .0.
  let vx: setvar x
  let vy: setvar y
  assume grpvlinv.b: |- B = ( Base ` G )
  assume grpvlinv.p: |- .+ = ( +g ` G )
  assume grpvlinv.n: |- N = ( invg ` G )
  assume grpvlinv.z: |- .0. = ( 0g ` G )


  assert |- ( ( G e. Grp /\ X e. ( B ^m I ) ) -> ( ( N o. X ) oF .+ X ) = ( I X. { .0. } ) )

  proof
    cG
    cgrp
    wcel
    #
    cX
    cB
    cI
    cmap
    co
    wcel
    #
    wa
    vy
    vx
    cI
    c.0
    c.pl
    cB
    cX
    cN
    cX
    ccom
    #
    cN
    cvv
    cB
    @1
    cI
    cvv
    wcel
    #
    @0
    @1
    cB
    cvv
    wcel
    @3
    cX
    cB
    cI
    elmapex
    simprd
    adantl
    @1
    cI
    cB
    cX
    wf
    #
    @0
    cX
    cB
    cI
    elmapi
    #
    adantl
    @0
    c.0
    cB
    wcel
    @1
    cB
    cG
    c.0
    grpvlinv.b
    grpvlinv.z
    grpidcl
    adantr
    @0
    cB
    cB
    cN
    wf
    #
    @1
    cB
    cG
    cN
    grpvlinv.b
    grpvlinv.n
    grpinvf
    #
    adantr
    @0
    @6
    @4
    @2
    vx
    cI
    vx
    cv
    cX
    cfv
    cN
    cfv
    cmpt
    wceq
    @1
    @7
    @5
    vx
    cN
    cX
    cI
    cB
    cB
    fcompt
    syl2an
    @0
    vy
    cv
    #
    cB
    wcel
    @8
    cN
    cfv
    @8
    c.pl
    co
    c.0
    wceq
    @1
    cB
    c.pl
    cG
    cN
    @8
    c.0
    grpvlinv.b
    grpvlinv.p
    grpvlinv.z
    grpvlinv.n
    grplinv
    adantlr
    caofinvl
end
