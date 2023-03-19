include "cgrp.mm"
include "wcel.mm"
include "cz.mm"
include "wa.mm"
include "cdvds.mm"
include "wbr.mm"
include "cv.mm"
include "cmg.mm"
include "cfv.mm"
include "co.mm"
include "c0g.mm"
include "wceq.mm"
include "wral.mm"
include "eqid.mm"
include "gexdvds.mm"
include "wb.mm"
include "oddvds.mm"
include "3expa.mm"
include "an32s.mm"
include "ralbidva.mm"
include "bitr4d.mm"

theorem gexdvds2
  let vx: setvar x
  let cE: class E
  let cG: class G
  let cN: class N
  let cO: class O
  let cX: class X
  assume gexod.1: |- X = ( Base ` G )
  assume gexod.2: |- E = ( gEx ` G )
  assume gexod.3: |- O = ( od ` G )

  disjoint E x
  disjoint G x
  disjoint N x
  disjoint X x
  assert |- ( ( G e. Grp /\ N e. ZZ ) -> ( E || N <-> A. x e. X ( O ` x ) || N ) )

  proof
    cG
    cgrp
    wcel
    #
    cN
    cz
    wcel
    #
    wa
    #
    cE
    cN
    cdvds
    wbr
    cN
    vx
    cv
    #
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
    vx
    cX
    wral
    @3
    cO
    cfv
    cN
    cdvds
    wbr
    #
    vx
    cX
    wral
    vx
    @4
    cE
    cG
    cN
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
    gexdvds
    @2
    @7
    @6
    vx
    cX
    @0
    @3
    cX
    wcel
    #
    @1
    @7
    @6
    wb
    #
    @0
    @10
    @1
    @11
    @3
    @4
    cG
    cN
    cO
    cX
    @5
    gexod.1
    gexod.3
    @8
    @9
    oddvds
    3expa
    an32s
    ralbidva
    bitr4d
end
