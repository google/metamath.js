include "cnvc.mm"
include "ccvs.mm"
include "cin.mm"
include "wcel.mm"
include "cngp.mm"
include "cv.mm"
include "co.mm"
include "cfv.mm"
include "cabs.mm"
include "cmul.mm"
include "wceq.mm"
include "wral.mm"
include "w3a.mm"
include "cr.mm"
include "wf.mm"
include "cc0.mm"
include "wb.mm"
include "caddc.mm"
include "cle.mm"
include "wbr.mm"
include "isncvsngp.mm"
include "simp1.mm"
include "nmf.mm"
include "3ad2ant2.mm"
include "cgrp.mm"
include "wa.mm"
include "wi.mm"
include "ngpi.mm"
include "r19.26.mm"
include "simpll.mm"
include "simplr.mm"
include "simpr.mm"
include "3jca.mm"
include "ralimi.mm"
include "sylbir.mm"
include "ex.mm"
include "3ad2ant3.mm"
include "syl.mm"
include "imp.mm"
include "3adant1.mm"
include "sylbi.mm"

theorem ncvsi
  let vx: setvar x
  let vy: setvar y
  let c.x: class .x.
  let vk: setvar k
  let cF: class F
  let cK: class K
  let c.mi: class .-
  let cN: class N
  let cV: class V
  let cW: class W
  let c.0: class .0.
  assume isncvsngp.v: |- V = ( Base ` W )
  assume isncvsngp.n: |- N = ( norm ` W )
  assume isncvsngp.s: |- .x. = ( .s ` W )
  assume isncvsngp.f: |- F = ( Scalar ` W )
  assume isncvsngp.k: |- K = ( Base ` F )
  assume ncvsi.m: |- .- = ( -g ` W )
  assume ncvsi.0: |- .0. = ( 0g ` W )

  disjoint F k
  disjoint F x
  disjoint k x
  disjoint K k
  disjoint K x
  disjoint N k
  disjoint N x
  disjoint V k
  disjoint V x
  disjoint W k
  disjoint W x
  disjoint .x. k
  disjoint .x. x
  disjoint V y
  disjoint W y
  disjoint x y
  assert |- ( W e. ( NrmVec i^i CVec ) -> ( W e. CVec /\ N : V --> RR /\ A. x e. V ( ( ( N ` x ) = 0 <-> x = .0. ) /\ A. y e. V ( N ` ( x .- y ) ) <_ ( ( N ` x ) + ( N ` y ) ) /\ A. k e. K ( N ` ( k .x. x ) ) = ( ( abs ` k ) x. ( N ` x ) ) ) ) )

  proof
    cW
    cnvc
    ccvs
    cin
    wcel
    cW
    ccvs
    wcel
    #
    cW
    cngp
    wcel
    #
    vk
    cv
    #
    vx
    cv
    #
    c.x
    co
    cN
    cfv
    @2
    cabs
    cfv
    @3
    cN
    cfv
    #
    cmul
    co
    wceq
    vk
    cK
    wral
    #
    vx
    cV
    wral
    #
    w3a
    #
    @0
    cV
    cr
    cN
    wf
    #
    @4
    cc0
    wceq
    @3
    c.0
    wceq
    wb
    #
    @3
    vy
    cv
    #
    c.mi
    co
    cN
    cfv
    @4
    @10
    cN
    cfv
    caddc
    co
    cle
    wbr
    vy
    cV
    wral
    #
    @5
    w3a
    #
    vx
    cV
    wral
    #
    w3a
    vx
    c.x
    vk
    cF
    cK
    cN
    cV
    cW
    isncvsngp.v
    isncvsngp.n
    isncvsngp.s
    isncvsngp.f
    isncvsngp.k
    isncvsngp
    @7
    @0
    @8
    @13
    @0
    @1
    @6
    simp1
    @1
    @0
    @8
    @6
    cW
    cN
    cV
    isncvsngp.v
    isncvsngp.n
    nmf
    3ad2ant2
    @1
    @6
    @13
    @0
    @1
    @6
    @13
    @1
    cW
    cgrp
    wcel
    #
    @8
    @9
    @11
    wa
    #
    vx
    cV
    wral
    #
    w3a
    @6
    @13
    wi
    #
    vx
    vy
    c.mi
    cN
    cV
    cW
    c.0
    isncvsngp.v
    isncvsngp.n
    ncvsi.m
    ncvsi.0
    ngpi
    @16
    @14
    @17
    @8
    @16
    @6
    @13
    @16
    @6
    wa
    @15
    @5
    wa
    #
    vx
    cV
    wral
    @13
    @15
    @5
    vx
    cV
    r19.26
    @18
    @12
    vx
    cV
    @18
    @9
    @11
    @5
    @9
    @11
    @5
    simpll
    @9
    @11
    @5
    simplr
    @15
    @5
    simpr
    3jca
    ralimi
    sylbir
    ex
    3ad2ant3
    syl
    imp
    3adant1
    3jca
    sylbi
end
