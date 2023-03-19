include "cgrp.mm"
include "wcel.mm"
include "cmap.mm"
include "co.mm"
include "wa.mm"
include "cv.mm"
include "cfv.mm"
include "cmpt.mm"
include "ccom.mm"
include "cof.mm"
include "csn.mm"
include "cxp.mm"
include "wceq.mm"
include "simpll.mm"
include "wf.mm"
include "elmapi.mm"
include "adantl.mm"
include "ffvelrnda.mm"
include "grprinv.mm"
include "syl2anc.mm"
include "mpteq2dva.mm"
include "cvv.mm"
include "elmapex.mm"
include "simprd.mm"
include "fvexd.mm"
include "feqmptd.mm"
include "grpinvf.mm"
include "fcompt.mm"
include "syl2an.mm"
include "offval2.mm"
include "fconstmpt.mm"
include "a1i.mm"
include "3eqtr4d.mm"

theorem grpvrinv
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


  assert |- ( ( G e. Grp /\ X e. ( B ^m I ) ) -> ( X oF .+ ( N o. X ) ) = ( I X. { .0. } ) )

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
    #
    vx
    cI
    vx
    cv
    #
    cX
    cfv
    #
    @4
    cN
    cfv
    #
    c.pl
    co
    #
    cmpt
    vx
    cI
    c.0
    cmpt
    #
    cX
    cN
    cX
    ccom
    #
    c.pl
    cof
    co
    cI
    c.0
    csn
    cxp
    #
    @2
    vx
    cI
    @6
    c.0
    @2
    @3
    cI
    wcel
    #
    wa
    #
    @0
    @4
    cB
    wcel
    @6
    c.0
    wceq
    @0
    @1
    @10
    simpll
    @2
    cI
    cB
    @3
    cX
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
    #
    ffvelrnda
    #
    cB
    c.pl
    cG
    cN
    @4
    c.0
    grpvlinv.b
    grpvlinv.p
    grpvlinv.z
    grpvlinv.n
    grprinv
    syl2anc
    mpteq2dva
    @2
    vx
    cI
    @4
    @5
    c.pl
    cX
    @8
    cvv
    cB
    cvv
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
    @16
    cX
    cB
    cI
    elmapex
    simprd
    adantl
    @15
    @11
    @4
    cN
    fvexd
    @2
    vx
    cI
    cB
    cX
    @14
    feqmptd
    @0
    cB
    cB
    cN
    wf
    @12
    @8
    vx
    cI
    @5
    cmpt
    wceq
    @1
    cB
    cG
    cN
    grpvlinv.b
    grpvlinv.n
    grpinvf
    @13
    vx
    cN
    cX
    cI
    cB
    cB
    fcompt
    syl2an
    offval2
    @9
    @7
    wceq
    @2
    vx
    cI
    c.0
    fconstmpt
    a1i
    3eqtr4d
end
