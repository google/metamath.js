include "wcel.mm"
include "wa.mm"
include "wne.mm"
include "w3a.mm"
include "cop.mm"
include "cpr.mm"
include "wfun.mm"
include "cdm.mm"
include "wceq.mm"
include "wfn.mm"
include "funprg.mm"
include "dmpropg.mm"
include "3ad2ant2.mm"
include "df-fn.mm"
include "sylanbrc.mm"

theorem fnprg
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y


  assert |- ( ( ( A e. V /\ B e. W ) /\ ( C e. X /\ D e. Y ) /\ A =/= B ) -> { <. A , C >. , <. B , D >. } Fn { A , B } )

  proof
    cA
    cV
    wcel
    cB
    cW
    wcel
    wa
    #
    cC
    cX
    wcel
    cD
    cY
    wcel
    wa
    #
    cA
    cB
    wne
    #
    w3a
    cA
    cC
    cop
    cB
    cD
    cop
    cpr
    #
    wfun
    @3
    cdm
    cA
    cB
    cpr
    #
    wceq
    #
    @3
    @4
    wfn
    cA
    cB
    cC
    cD
    cV
    cW
    cX
    cY
    funprg
    @1
    @0
    @5
    @2
    cA
    cC
    cB
    cD
    cX
    cY
    dmpropg
    3ad2ant2
    @3
    @4
    df-fn
    sylanbrc
end
