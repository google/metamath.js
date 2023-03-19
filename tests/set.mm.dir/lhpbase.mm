include "cvv.mm"
include "wcel.mm"
include "clh.mm"
include "cfv.mm"
include "c0.mm"
include "wceq.mm"
include "n0i.mm"
include "eqeq1i.mm"
include "sylnib.mm"
include "fvprc.mm"
include "nsyl2.mm"
include "cp1.mm"
include "ccvr.mm"
include "wbr.mm"
include "eqid.mm"
include "islhp.mm"
include "simprbda.mm"
include "mpancom.mm"

theorem lhpbase
  let cB: class B
  let cH: class H
  let cK: class K
  let cW: class W
  assume lhpbase.b: |- B = ( Base ` K )
  assume lhpbase.h: |- H = ( LHyp ` K )


  assert |- ( W e. H -> W e. B )

  proof
    cK
    cvv
    wcel
    #
    cW
    cH
    wcel
    #
    cW
    cB
    wcel
    #
    @1
    cK
    clh
    cfv
    #
    c0
    wceq
    #
    @0
    @1
    cH
    c0
    wceq
    @4
    cH
    cW
    n0i
    cH
    @3
    c0
    lhpbase.h
    eqeq1i
    sylnib
    cK
    clh
    fvprc
    nsyl2
    @0
    @1
    @2
    cW
    cK
    cp1
    cfv
    #
    cK
    ccvr
    cfv
    #
    wbr
    cvv
    cB
    @6
    @5
    cH
    cK
    cW
    lhpbase.b
    @5
    eqid
    @6
    eqid
    lhpbase.h
    islhp
    simprbda
    mpancom
end
