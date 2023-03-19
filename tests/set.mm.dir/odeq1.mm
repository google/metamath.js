include "cgrp.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "c1.mm"
include "wceq.mm"
include "cmg.mm"
include "co.mm"
include "oveq1.mm"
include "eqcomd.mm"
include "wb.mm"
include "eqid.mm"
include "mulg1.mm"
include "odid.mm"
include "eqeq12d.mm"
include "adantl.mm"
include "syl5ib.mm"
include "od1.mm"
include "adantr.mm"
include "fveq2.mm"
include "eqeq1d.mm"
include "syl5ibrcom.mm"
include "impbid.mm"

theorem odeq1
  let cA: class A
  let cG: class G
  let cO: class O
  let cX: class X
  let c.0: class .0.
  assume od1.1: |- O = ( od ` G )
  assume od1.2: |- .0. = ( 0g ` G )
  assume odeq1.3: |- X = ( Base ` G )


  assert |- ( ( G e. Grp /\ A e. X ) -> ( ( O ` A ) = 1 <-> A = .0. ) )

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
    #
    c1
    wceq
    #
    cA
    c.0
    wceq
    #
    @4
    c1
    cA
    cG
    cmg
    cfv
    #
    co
    #
    @3
    cA
    @6
    co
    #
    wceq
    #
    @2
    @5
    @4
    @8
    @7
    @3
    c1
    cA
    @6
    oveq1
    eqcomd
    @1
    @9
    @5
    wb
    @0
    @1
    @7
    cA
    @8
    c.0
    cX
    @6
    cG
    cA
    odeq1.3
    @6
    eqid
    #
    mulg1
    cA
    @6
    cG
    cO
    cX
    c.0
    odeq1.3
    od1.1
    @10
    od1.2
    odid
    eqeq12d
    adantl
    syl5ib
    @2
    @4
    @5
    c.0
    cO
    cfv
    #
    c1
    wceq
    #
    @0
    @12
    @1
    cG
    cO
    c.0
    od1.1
    od1.2
    od1
    adantr
    @5
    @3
    @11
    c1
    cA
    c.0
    cO
    fveq2
    eqeq1d
    syl5ibrcom
    impbid
end
