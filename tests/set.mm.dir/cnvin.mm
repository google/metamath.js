include "cdif.mm"
include "ccnv.mm"
include "cin.mm"
include "cnvdif.mm"
include "difeq2i.mm"
include "eqtri.mm"
include "dfin4.mm"
include "cnveqi.mm"
include "3eqtr4i.mm"

theorem cnvin
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y


  assert |- `' ( A i^i B ) = ( `' A i^i `' B )

  proof
    cA
    cA
    cB
    cdif
    #
    cdif
    #
    ccnv
    #
    cA
    ccnv
    #
    @3
    cB
    ccnv
    #
    cdif
    #
    cdif
    #
    cA
    cB
    cin
    #
    ccnv
    @3
    @4
    cin
    @2
    @3
    @0
    ccnv
    #
    cdif
    @6
    cA
    @0
    cnvdif
    @8
    @5
    @3
    cA
    cB
    cnvdif
    difeq2i
    eqtri
    @7
    @1
    cA
    cB
    dfin4
    cnveqi
    @3
    @4
    dfin4
    3eqtr4i
end
