include "cgrp.mm"
include "wcel.mm"
include "cz.mm"
include "w3a.mm"
include "co.mm"
include "cfv.mm"
include "cdvds.mm"
include "wbr.mm"
include "cmul.mm"
include "odcl.mm"
include "nn0zd.mm"
include "3ad2ant2.mm"
include "simp3.mm"
include "dvdsmul1.mm"
include "syl2anc.mm"
include "wb.mm"
include "odmulgid.mm"
include "mpdan.mm"
include "mpbird.mm"

theorem odmulg2
  let cA: class A
  let c.x: class .x.
  let cG: class G
  let cN: class N
  let cO: class O
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  assume odmulgid.1: |- X = ( Base ` G )
  assume odmulgid.2: |- O = ( od ` G )
  assume odmulgid.3: |- .x. = ( .g ` G )


  assert |- ( ( G e. Grp /\ A e. X /\ N e. ZZ ) -> ( O ` ( N .x. A ) ) || ( O ` A ) )

  proof
    cG
    cgrp
    wcel
    #
    cA
    cX
    wcel
    #
    cN
    cz
    wcel
    #
    w3a
    #
    cN
    cA
    c.x
    co
    cO
    cfv
    cA
    cO
    cfv
    #
    cdvds
    wbr
    #
    @4
    @4
    cN
    cmul
    co
    cdvds
    wbr
    #
    @3
    @4
    cz
    wcel
    #
    @2
    @6
    @1
    @0
    @7
    @2
    @1
    @4
    cA
    cG
    cO
    cX
    odmulgid.1
    odmulgid.2
    odcl
    nn0zd
    3ad2ant2
    #
    @0
    @1
    @2
    simp3
    @4
    cN
    dvdsmul1
    syl2anc
    @3
    @7
    @5
    @6
    wb
    @8
    cA
    c.x
    cG
    @4
    cN
    cO
    cX
    odmulgid.1
    odmulgid.2
    odmulgid.3
    odmulgid
    mpdan
    mpbird
end
