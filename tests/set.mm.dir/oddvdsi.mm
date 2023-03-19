include "cgrp.mm"
include "wcel.mm"
include "cfv.mm"
include "cdvds.mm"
include "wbr.mm"
include "w3a.mm"
include "co.mm"
include "wceq.mm"
include "simp3.mm"
include "cz.mm"
include "wb.mm"
include "dvdszrcl.mm"
include "simprd.mm"
include "oddvds.mm"
include "syl3an3.mm"
include "mpbid.mm"

theorem oddvdsi
  let cA: class A
  let c.x: class .x.
  let cG: class G
  let cN: class N
  let cO: class O
  let cX: class X
  let c.0: class .0.
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let vx: setvar x
  assume odcl.1: |- X = ( Base ` G )
  assume odcl.2: |- O = ( od ` G )
  assume odid.3: |- .x. = ( .g ` G )
  assume odid.4: |- .0. = ( 0g ` G )


  assert |- ( ( G e. Grp /\ A e. X /\ ( O ` A ) || N ) -> ( N .x. A ) = .0. )

  proof
    cG
    cgrp
    wcel
    #
    cA
    cX
    wcel
    #
    cA
    cO
    cfv
    #
    cN
    cdvds
    wbr
    #
    w3a
    @3
    cN
    cA
    c.x
    co
    c.0
    wceq
    #
    @0
    @1
    @3
    simp3
    @3
    @0
    @1
    cN
    cz
    wcel
    #
    @3
    @4
    wb
    @3
    @2
    cz
    wcel
    @5
    @2
    cN
    dvdszrcl
    simprd
    cA
    c.x
    cG
    cN
    cO
    cX
    c.0
    odcl.1
    odcl.2
    odid.3
    odid.4
    oddvds
    syl3an3
    mpbid
end
