include "wiso.mm"
include "wse.mm"
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
include "isoselem.mm"
include "ccnv.mm"
include "isocnv.mm"
include "4syl.mm"
include "impbid.mm"

theorem isose
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cH: class H
  let vx: setvar x
  let cV: class V


  assert |- ( H Isom R , S ( A , B ) -> ( R Se A <-> S Se B ) )

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
    wse
    cB
    cS
    wse
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
    vx
    cv
    #
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
    @1
    vx
    vex
    #
    funimaex
    3syl
    isoselem
    @0
    vx
    cB
    cA
    cS
    cR
    cH
    ccnv
    #
    cA
    cB
    cR
    cS
    cH
    isocnv
    #
    @0
    cB
    cA
    cS
    cR
    @3
    wiso
    cB
    cA
    @3
    wf1o
    @3
    wfun
    @3
    @1
    cima
    cvv
    wcel
    @4
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
    @1
    @2
    funimaex
    4syl
    isoselem
    impbid
end
