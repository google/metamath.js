include "wiso.mm"
include "wcel.mm"
include "wa.mm"
include "simpl.mm"
include "cv.mm"
include "cima.mm"
include "wss.mm"
include "cvv.mm"
include "crn.mm"
include "imassrn.mm"
include "wf1o.mm"
include "wf.mm"
include "isof1o.mm"
include "f1of.mm"
include "frn.mm"
include "3syl.mm"
include "syl5ss.mm"
include "ssexg.mm"
include "sylan.mm"
include "isofrlem.mm"

theorem isofr2
  let cA: class A
  let cB: class B
  let cR: class R
  let cS: class S
  let cH: class H
  let cV: class V
  let vx: setvar x


  assert |- ( ( H Isom R , S ( A , B ) /\ B e. V ) -> ( S Fr B -> R Fr A ) )

  proof
    cA
    cB
    cR
    cS
    cH
    wiso
    #
    cB
    cV
    wcel
    #
    wa
    vx
    cA
    cB
    cR
    cS
    cH
    @0
    @1
    simpl
    @0
    cH
    vx
    cv
    #
    cima
    #
    cB
    wss
    @1
    @3
    cvv
    wcel
    @0
    @3
    cH
    crn
    #
    cB
    cH
    @2
    imassrn
    @0
    cA
    cB
    cH
    wf1o
    cA
    cB
    cH
    wf
    @4
    cB
    wss
    cA
    cB
    cR
    cS
    cH
    isof1o
    cA
    cB
    cH
    f1of
    cA
    cB
    cH
    frn
    3syl
    syl5ss
    @3
    cB
    cV
    ssexg
    sylan
    isofrlem
end
