include "cngp.mm"
include "wcel.mm"
include "cgrp.mm"
include "cr.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "wb.mm"
include "co.mm"
include "caddc.mm"
include "cle.mm"
include "wbr.mm"
include "wral.mm"
include "wa.mm"
include "ngpgrp.mm"
include "nmf.mm"
include "nmeq0.mm"
include "nmmtri.mm"
include "3expa.mm"
include "ralrimiva.mm"
include "jca.mm"
include "3jca.mm"

theorem ngpi
  let vx: setvar x
  let vy: setvar y
  let c.mi: class .-
  let cN: class N
  let cV: class V
  let cW: class W
  let c.0: class .0.
  assume ngpi.v: |- V = ( Base ` W )
  assume ngpi.n: |- N = ( norm ` W )
  assume ngpi.m: |- .- = ( -g ` W )
  assume ngpi.0: |- .0. = ( 0g ` W )

  disjoint V y
  disjoint W x
  disjoint W y
  disjoint x y
  assert |- ( W e. NrmGrp -> ( W e. Grp /\ N : V --> RR /\ A. x e. V ( ( ( N ` x ) = 0 <-> x = .0. ) /\ A. y e. V ( N ` ( x .- y ) ) <_ ( ( N ` x ) + ( N ` y ) ) ) ) )

  proof
    cW
    cngp
    wcel
    #
    cW
    cgrp
    wcel
    cV
    cr
    cN
    wf
    vx
    cv
    #
    cN
    cfv
    #
    cc0
    wceq
    @1
    c.0
    wceq
    wb
    #
    @1
    vy
    cv
    #
    c.mi
    co
    cN
    cfv
    @2
    @4
    cN
    cfv
    caddc
    co
    cle
    wbr
    #
    vy
    cV
    wral
    #
    wa
    #
    vx
    cV
    wral
    cW
    ngpgrp
    cW
    cN
    cV
    ngpi.v
    ngpi.n
    nmf
    @0
    @7
    vx
    cV
    @0
    @1
    cV
    wcel
    #
    wa
    #
    @3
    @6
    @1
    cW
    cN
    cV
    c.0
    ngpi.v
    ngpi.n
    ngpi.0
    nmeq0
    @9
    @5
    vy
    cV
    @0
    @8
    @4
    cV
    wcel
    @5
    @1
    @4
    cW
    c.mi
    cN
    cV
    ngpi.v
    ngpi.n
    ngpi.m
    nmmtri
    3expa
    ralrimiva
    jca
    ralrimiva
    3jca
end
