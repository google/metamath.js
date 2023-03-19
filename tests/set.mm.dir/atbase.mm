include "cvv.mm"
include "wcel.mm"
include "catm.mm"
include "cfv.mm"
include "c0.mm"
include "wceq.mm"
include "n0i.mm"
include "eqeq1i.mm"
include "sylnib.mm"
include "fvprc.mm"
include "nsyl2.mm"
include "cp0.mm"
include "ccvr.mm"
include "wbr.mm"
include "eqid.mm"
include "isat.mm"
include "simprbda.mm"
include "mpancom.mm"

theorem atbase
  let cA: class A
  let cB: class B
  let cP: class P
  let cK: class K
  assume atombase.b: |- B = ( Base ` K )
  assume atombase.a: |- A = ( Atoms ` K )


  assert |- ( P e. A -> P e. B )

  proof
    cK
    cvv
    wcel
    #
    cP
    cA
    wcel
    #
    cP
    cB
    wcel
    #
    @1
    cK
    catm
    cfv
    #
    c0
    wceq
    #
    @0
    @1
    cA
    c0
    wceq
    @4
    cA
    cP
    n0i
    cA
    @3
    c0
    atombase.a
    eqeq1i
    sylnib
    cK
    catm
    fvprc
    nsyl2
    @0
    @1
    @2
    cK
    cp0
    cfv
    #
    cP
    cK
    ccvr
    cfv
    #
    wbr
    cA
    cB
    @6
    cvv
    cP
    cK
    @5
    atombase.b
    @5
    eqid
    @6
    eqid
    atombase.a
    isat
    simprbda
    mpancom
end
