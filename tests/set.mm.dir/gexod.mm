include "cgrp.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cdvds.mm"
include "wbr.mm"
include "cmg.mm"
include "co.mm"
include "c0g.mm"
include "wceq.mm"
include "eqid.mm"
include "gexid.mm"
include "adantl.mm"
include "cz.mm"
include "wb.mm"
include "cn0.mm"
include "gexcl.mm"
include "adantr.mm"
include "nn0zd.mm"
include "oddvds.mm"
include "mpd3an3.mm"
include "mpbird.mm"

theorem gexod
  let cA: class A
  let cE: class E
  let cG: class G
  let cO: class O
  let cX: class X
  let vx: setvar x
  let cN: class N
  assume gexod.1: |- X = ( Base ` G )
  assume gexod.2: |- E = ( gEx ` G )
  assume gexod.3: |- O = ( od ` G )


  assert |- ( ( G e. Grp /\ A e. X ) -> ( O ` A ) || E )

  proof
    cG
    cgrp
    wcel
    #
    cA
    cX
    wcel
    #
    wa
    #
    cA
    cO
    cfv
    cE
    cdvds
    wbr
    #
    cE
    cA
    cG
    cmg
    cfv
    #
    co
    cG
    c0g
    cfv
    #
    wceq
    #
    @1
    @6
    @0
    cA
    @4
    cE
    cG
    cX
    @5
    gexod.1
    gexod.2
    @4
    eqid
    #
    @5
    eqid
    #
    gexid
    adantl
    @0
    @1
    cE
    cz
    wcel
    @3
    @6
    wb
    @2
    cE
    @0
    cE
    cn0
    wcel
    @1
    cE
    cG
    cgrp
    cX
    gexod.1
    gexod.2
    gexcl
    adantr
    nn0zd
    cA
    @4
    cG
    cE
    cO
    cX
    @5
    gexod.1
    gexod.3
    @7
    @8
    oddvds
    mpd3an3
    mpbird
end
