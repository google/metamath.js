include "chlt.mm"
include "wcel.mm"
include "wa.mm"
include "wbr.mm"
include "cfv.mm"
include "cp0.mm"
include "cops.mm"
include "wb.mm"
include "hlop.mm"
include "adantr.mm"
include "simpr.mm"
include "op1cl.mm"
include "syl.mm"
include "cvrcon3b.mm"
include "syl3anc.mm"
include "wceq.mm"
include "eqid.mm"
include "opoc1.mm"
include "breq1d.mm"
include "opoccl.mm"
include "sylan.mm"
include "biantrurd.mm"
include "3bitrd.mm"
include "isat.mm"
include "bitr4d.mm"

theorem 1cvrco
  let cA: class A
  let cB: class B
  let cC: class C
  let c.1: class .1.
  let cK: class K
  let c.pe: class ._|_
  let cX: class X
  assume 1cvrco.b: |- B = ( Base ` K )
  assume 1cvrco.u: |- .1. = ( 1. ` K )
  assume 1cvrco.o: |- ._|_ = ( oc ` K )
  assume 1cvrco.c: |- C = ( <o ` K )
  assume 1cvrco.a: |- A = ( Atoms ` K )


  assert |- ( ( K e. HL /\ X e. B ) -> ( X C .1. <-> ( ._|_ ` X ) e. A ) )

  proof
    cK
    chlt
    wcel
    #
    cX
    cB
    wcel
    #
    wa
    #
    cX
    c.1
    cC
    wbr
    #
    cX
    c.pe
    cfv
    #
    cB
    wcel
    #
    cK
    cp0
    cfv
    #
    @4
    cC
    wbr
    #
    wa
    #
    @4
    cA
    wcel
    #
    @2
    @3
    c.1
    c.pe
    cfv
    #
    @4
    cC
    wbr
    #
    @7
    @8
    @2
    cK
    cops
    wcel
    #
    @1
    c.1
    cB
    wcel
    #
    @3
    @11
    wb
    @0
    @12
    @1
    cK
    hlop
    #
    adantr
    #
    @0
    @1
    simpr
    @2
    @12
    @13
    @15
    cB
    c.1
    cK
    1cvrco.b
    1cvrco.u
    op1cl
    syl
    cB
    cC
    cK
    c.pe
    cX
    c.1
    1cvrco.b
    1cvrco.o
    1cvrco.c
    cvrcon3b
    syl3anc
    @2
    @10
    @6
    @4
    cC
    @2
    @12
    @10
    @6
    wceq
    @15
    c.1
    cK
    c.pe
    @6
    @6
    eqid
    #
    1cvrco.u
    1cvrco.o
    opoc1
    syl
    breq1d
    @2
    @5
    @7
    @0
    @12
    @1
    @5
    @14
    cB
    cK
    c.pe
    cX
    1cvrco.b
    1cvrco.o
    opoccl
    sylan
    biantrurd
    3bitrd
    @0
    @9
    @8
    wb
    @1
    cA
    cB
    cC
    chlt
    @4
    cK
    @6
    1cvrco.b
    @16
    1cvrco.c
    1cvrco.a
    isat
    adantr
    bitr4d
end
