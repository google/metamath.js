include "wcel.mm"
include "wfun.mm"
include "wa.mm"
include "cedg.mm"
include "cfv.mm"
include "crn.mm"
include "cv.mm"
include "wceq.mm"
include "cdm.mm"
include "wrex.mm"
include "ciedg.mm"
include "edgvalOLD.mm"
include "adantr.mm"
include "eqcomi.mm"
include "a1i.mm"
include "rneqd.mm"
include "eqtrd.mm"
include "eleq2d.mm"
include "wb.mm"
include "elrnrexdmb.mm"
include "adantl.mm"
include "bitrd.mm"

theorem edgiedgbOLD
  let vx: setvar x
  let cE: class E
  let cG: class G
  let cI: class I
  let cW: class W
  assume edgiedgb.i: |- I = ( iEdg ` G )

  disjoint E x
  disjoint I x
  assert |- ( ( G e. W /\ Fun I ) -> ( E e. ( Edg ` G ) <-> E. x e. dom I E = ( I ` x ) ) )

  proof
    cG
    cW
    wcel
    #
    cI
    wfun
    #
    wa
    #
    cE
    cG
    cedg
    cfv
    #
    wcel
    cE
    cI
    crn
    #
    wcel
    #
    cE
    vx
    cv
    cI
    cfv
    wceq
    vx
    cI
    cdm
    wrex
    #
    @2
    @3
    @4
    cE
    @2
    @3
    cG
    ciedg
    cfv
    #
    crn
    #
    @4
    @0
    @3
    @8
    wceq
    @1
    cG
    cW
    edgvalOLD
    adantr
    @2
    @7
    cI
    @7
    cI
    wceq
    @2
    cI
    @7
    edgiedgb.i
    eqcomi
    a1i
    rneqd
    eqtrd
    eleq2d
    @1
    @5
    @6
    wb
    @0
    vx
    cI
    cE
    elrnrexdmb
    adantl
    bitrd
end
