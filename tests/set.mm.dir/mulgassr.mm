include "cgrp.mm"
include "wcel.mm"
include "cz.mm"
include "w3a.mm"
include "wa.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "cc.mm"
include "zcn.mm"
include "3ad2ant2.mm"
include "3ad2ant1.mm"
include "mulcomd.mm"
include "adantl.mm"
include "oveq1d.mm"
include "mulgass.mm"
include "eqtrd.mm"

theorem mulgassr
  let cB: class B
  let c.x: class .x.
  let cG: class G
  let cM: class M
  let cN: class N
  let cX: class X
  let vm: setvar m
  let vn: setvar n
  assume mulgass.b: |- B = ( Base ` G )
  assume mulgass.t: |- .x. = ( .g ` G )


  assert |- ( ( G e. Grp /\ ( M e. ZZ /\ N e. ZZ /\ X e. B ) ) -> ( ( N x. M ) .x. X ) = ( M .x. ( N .x. X ) ) )

  proof
    cG
    cgrp
    wcel
    #
    cM
    cz
    wcel
    #
    cN
    cz
    wcel
    #
    cX
    cB
    wcel
    #
    w3a
    #
    wa
    #
    cN
    cM
    cmul
    co
    #
    cX
    c.x
    co
    cM
    cN
    cmul
    co
    #
    cX
    c.x
    co
    cM
    cN
    cX
    c.x
    co
    c.x
    co
    @5
    @6
    @7
    cX
    c.x
    @4
    @6
    @7
    wceq
    @0
    @4
    cN
    cM
    @2
    @1
    cN
    cc
    wcel
    @3
    cN
    zcn
    3ad2ant2
    @1
    @2
    cM
    cc
    wcel
    @3
    cM
    zcn
    3ad2ant1
    mulcomd
    adantl
    oveq1d
    cB
    c.x
    cG
    cM
    cN
    cX
    mulgass.b
    mulgass.t
    mulgass
    eqtrd
end
