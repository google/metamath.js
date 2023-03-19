include "chlt.mm"
include "wcel.mm"
include "coml.mm"
include "ccla.mm"
include "clc.mm"
include "w3a.mm"
include "co.mm"
include "wceq.mm"
include "wbr.mm"
include "wb.mm"
include "hlomcmcv.mm"
include "cvlcvrp.mm"
include "syl3an1.mm"

theorem cvrp
  let cA: class A
  let cB: class B
  let cC: class C
  let cP: class P
  let c.or: class .\/
  let cK: class K
  let c.an: class ./\
  let cX: class X
  let c.0: class .0.
  assume cvrp.b: |- B = ( Base ` K )
  assume cvrp.j: |- .\/ = ( join ` K )
  assume cvrp.m: |- ./\ = ( meet ` K )
  assume cvrp.z: |- .0. = ( 0. ` K )
  assume cvrp.c: |- C = ( <o ` K )
  assume cvrp.a: |- A = ( Atoms ` K )


  assert |- ( ( K e. HL /\ X e. B /\ P e. A ) -> ( ( X ./\ P ) = .0. <-> X C ( X .\/ P ) ) )

  proof
    cK
    chlt
    wcel
    cK
    coml
    wcel
    cK
    ccla
    wcel
    cK
    clc
    wcel
    w3a
    cX
    cB
    wcel
    cP
    cA
    wcel
    cX
    cP
    c.an
    co
    c.0
    wceq
    cX
    cX
    cP
    c.or
    co
    cC
    wbr
    wb
    cK
    hlomcmcv
    cA
    cB
    cC
    cP
    c.or
    cK
    c.an
    cX
    c.0
    cvrp.b
    cvrp.j
    cvrp.m
    cvrp.z
    cvrp.c
    cvrp.a
    cvlcvrp
    syl3an1
end
