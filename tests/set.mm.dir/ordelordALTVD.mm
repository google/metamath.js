include "word.mm"
include "wcel.mm"
include "wa.mm"
include "wtr.mm"
include "cv.mm"
include "wceq.mm"
include "w3o.mm"
include "wral.mm"
include "idn1.mm"
include "simpl.mm"
include "e1a.mm"
include "ordtr.mm"
include "dford2.mm"
include "simprbi.mm"
include "wb.mm"
include "wal.mm"
include "3orcomb.mm"
include "ax-gen.mm"
include "alral.mm"
include "e0a.mm"
include "ralbi.mm"
include "e1bi.mm"
include "simpr.mm"
include "tratrb.mm"
include "3exp.mm"
include "e111.mm"
include "wss.mm"
include "trss.mm"
include "e11.mm"
include "wi.mm"
include "ssralv2.mm"
include "ex.mm"
include "simplbi2.mm"
include "in1.mm"

theorem ordelordALTVD
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( Ord A /\ B e. A ) -> Ord B )

  proof
    cA
    word
    #
    cB
    cA
    wcel
    #
    wa
    #
    cB
    word
    #
    @2
    cB
    wtr
    #
    vx
    cv
    #
    vy
    cv
    #
    wcel
    #
    @5
    @6
    wceq
    #
    @6
    @5
    wcel
    #
    w3o
    #
    vy
    cB
    wral
    vx
    cB
    wral
    #
    @3
    @2
    cA
    wtr
    #
    @7
    @9
    @8
    w3o
    #
    vy
    cA
    wral
    #
    vx
    cA
    wral
    #
    @1
    @4
    @2
    @0
    @12
    @2
    @2
    @0
    @2
    idn1
    #
    @0
    @1
    simpl
    e1a
    #
    cA
    ordtr
    e1a
    #
    @2
    @10
    vy
    cA
    wral
    #
    vx
    cA
    wral
    #
    @15
    @2
    @0
    @20
    @17
    @0
    @12
    @20
    vx
    vy
    cA
    dford2
    simprbi
    e1a
    #
    @19
    @14
    wb
    #
    vx
    cA
    wral
    #
    @20
    @15
    wb
    @22
    vx
    wal
    @23
    @22
    vx
    @10
    @13
    wb
    #
    vy
    cA
    wral
    #
    @22
    @24
    vy
    wal
    @25
    @24
    vy
    @7
    @8
    @9
    3orcomb
    ax-gen
    @24
    vy
    cA
    alral
    e0a
    @10
    @13
    vy
    cA
    ralbi
    e0a
    ax-gen
    @22
    vx
    cA
    alral
    e0a
    @19
    @14
    vx
    cA
    ralbi
    e0a
    e1bi
    @2
    @2
    @1
    @16
    @0
    @1
    simpr
    e1a
    #
    @12
    @15
    @1
    @4
    vx
    vy
    cA
    cB
    tratrb
    3exp
    e111
    @2
    cB
    cA
    wss
    #
    @27
    @20
    @11
    @2
    @12
    @1
    @27
    @18
    @26
    cA
    cB
    trss
    e11
    #
    @28
    @21
    @27
    @27
    @20
    @11
    wi
    @10
    vx
    vy
    cB
    cA
    cB
    cA
    ssralv2
    ex
    e111
    @3
    @4
    @11
    vx
    vy
    cB
    dford2
    simplbi2
    e11
    in1
end
