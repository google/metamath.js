include "ctgp.mm"
include "wcel.mm"
include "cgrp.mm"
include "ctmd.mm"
include "cminusg.mm"
include "cfv.mm"
include "ctopn.mm"
include "ccn.mm"
include "co.mm"
include "tgpgrp.mm"
include "oppggrp.mm"
include "syl.mm"
include "tgptmd.mm"
include "oppgtmd.mm"
include "wceq.mm"
include "eqid.mm"
include "oppginv.mm"
include "tgpinv.mm"
include "eqeltrrd.mm"
include "oppgtopn.mm"
include "istgp.mm"
include "syl3anbrc.mm"

theorem oppgtgp
  let cG: class G
  let cO: class O
  let vx: setvar x
  let vy: setvar y
  assume oppgtmd.1: |- O = ( oppG ` G )


  assert |- ( G e. TopGrp -> O e. TopGrp )

  proof
    cG
    ctgp
    wcel
    #
    cO
    cgrp
    wcel
    #
    cO
    ctmd
    wcel
    #
    cO
    cminusg
    cfv
    #
    cG
    ctopn
    cfv
    #
    @4
    ccn
    co
    #
    wcel
    cO
    ctgp
    wcel
    @0
    cG
    cgrp
    wcel
    #
    @1
    cG
    tgpgrp
    #
    cG
    cO
    oppgtmd.1
    oppggrp
    syl
    @0
    cG
    ctmd
    wcel
    @2
    cG
    tgptmd
    cG
    cO
    oppgtmd.1
    oppgtmd
    syl
    @0
    cG
    cminusg
    cfv
    #
    @3
    @5
    @0
    @6
    @8
    @3
    wceq
    @7
    cG
    @8
    cO
    oppgtmd.1
    @8
    eqid
    #
    oppginv
    syl
    cG
    @8
    @4
    @4
    eqid
    #
    @9
    tgpinv
    eqeltrrd
    cO
    @3
    @4
    cG
    @4
    cO
    oppgtmd.1
    @10
    oppgtopn
    @3
    eqid
    istgp
    syl3anbrc
end
