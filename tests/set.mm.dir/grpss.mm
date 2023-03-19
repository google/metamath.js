include "cgrp.mm"
include "wcel.mm"
include "cbs.mm"
include "baseid.mm"
include "cnx.mm"
include "cfv.mm"
include "cop.mm"
include "cplusg.mm"
include "cpr.mm"
include "opex.mm"
include "prid1.mm"
include "eleqtrri.mm"
include "strss.mm"
include "plusgid.mm"
include "prid2.mm"
include "grpprop.mm"
include "bicomi.mm"

theorem grpss
  let cB: class B
  let c.pl: class .+
  let cR: class R
  let cG: class G
  assume grpss.g: |- G = { <. ( Base ` ndx ) , B >. , <. ( +g ` ndx ) , .+ >. }
  assume grpss.r: |- R e. _V
  assume grpss.s: |- G C_ R
  assume grpss.f: |- Fun R


  assert |- ( G e. Grp <-> R e. Grp )

  proof
    cR
    cgrp
    wcel
    cG
    cgrp
    wcel
    cR
    cG
    cB
    cG
    cR
    cbs
    grpss.r
    grpss.f
    grpss.s
    baseid
    cnx
    cbs
    cfv
    #
    cB
    cop
    #
    @1
    cnx
    cplusg
    cfv
    #
    c.pl
    cop
    #
    cpr
    #
    cG
    @1
    @3
    @0
    cB
    opex
    prid1
    grpss.g
    eleqtrri
    strss
    c.pl
    cG
    cR
    cplusg
    grpss.r
    grpss.f
    grpss.s
    plusgid
    @3
    @4
    cG
    @1
    @3
    @2
    c.pl
    opex
    prid2
    grpss.g
    eleqtrri
    strss
    grpprop
    bicomi
end
