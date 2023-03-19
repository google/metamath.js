include "wiso.mm"
include "wfr.mm"
include "ccnv.mm"
include "wi.mm"
include "isocnv.mm"
include "id.mm"
include "wf1o.mm"
include "wfun.mm"
include "cv.mm"
include "cima.mm"
include "cvv.mm"
include "wcel.mm"
include "isof1o.mm"
include "f1ofun.mm"
include "vex.mm"
include "funimaex.mm"
include "3syl.mm"
include "isofrlem.mm"
include "syl.mm"
include "impbid.mm"

theorem isofr
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cH: class H
  let vx: setvar x
  let cV: class V


  assert |- ( H Isom R , S ( A , B ) -> ( R Fr A <-> S Fr B ) )

  proof
    cA
    cB
    cR
    cS
    cH
    wiso
    #
    cA
    cR
    wfr
    #
    cB
    cS
    wfr
    #
    @0
    cB
    cA
    cS
    cR
    cH
    ccnv
    #
    wiso
    #
    @1
    @2
    wi
    cA
    cB
    cR
    cS
    cH
    isocnv
    @4
    vx
    cB
    cA
    cS
    cR
    @3
    @4
    id
    @4
    cB
    cA
    @3
    wf1o
    @3
    wfun
    @3
    vx
    cv
    #
    cima
    cvv
    wcel
    cB
    cA
    cS
    cR
    @3
    isof1o
    cB
    cA
    @3
    f1ofun
    @3
    @5
    vx
    vex
    #
    funimaex
    3syl
    isofrlem
    syl
    @0
    vx
    cA
    cB
    cR
    cS
    cH
    @0
    id
    @0
    cA
    cB
    cH
    wf1o
    cH
    wfun
    cH
    @5
    cima
    cvv
    wcel
    cA
    cB
    cR
    cS
    cH
    isof1o
    cA
    cB
    cH
    f1ofun
    cH
    @5
    @6
    funimaex
    3syl
    isofrlem
    impbid
end
