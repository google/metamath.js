include "wfun.mm"
include "c0.mm"
include "wceq.mm"
include "ciedg.mm"
include "cfv.mm"
include "crn.mm"
include "wb.mm"
include "cedg.mm"
include "edgval.mm"
include "eqtri.mm"
include "eqeq1i.mm"
include "a1i.mm"
include "eqcomi.mm"
include "rneqi.mm"
include "wrel.mm"
include "funrel.mm"
include "relrn0.mm"
include "bicomd.mm"
include "syl.mm"
include "3bitrd.mm"

theorem edg0iedg0
  let cE: class E
  let cG: class G
  let cI: class I
  assume edg0iedg0.i: |- I = ( iEdg ` G )
  assume edg0iedg0.e: |- E = ( Edg ` G )


  assert |- ( Fun I -> ( E = (/) <-> I = (/) ) )

  proof
    cI
    wfun
    #
    cE
    c0
    wceq
    #
    cG
    ciedg
    cfv
    #
    crn
    #
    c0
    wceq
    #
    cI
    crn
    #
    c0
    wceq
    #
    cI
    c0
    wceq
    #
    @1
    @4
    wb
    @0
    cE
    @3
    c0
    cE
    cG
    cedg
    cfv
    @3
    edg0iedg0.e
    cG
    edgval
    eqtri
    eqeq1i
    a1i
    @4
    @6
    wb
    @0
    @3
    @5
    c0
    @2
    cI
    cI
    @2
    edg0iedg0.i
    eqcomi
    rneqi
    eqeq1i
    a1i
    @0
    cI
    wrel
    #
    @6
    @7
    wb
    cI
    funrel
    @8
    @7
    @6
    cI
    relrn0
    bicomd
    syl
    3bitrd
end
