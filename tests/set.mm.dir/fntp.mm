include "wne.mm"
include "w3a.mm"
include "cop.mm"
include "ctp.mm"
include "wfun.mm"
include "cdm.mm"
include "wceq.mm"
include "wfn.mm"
include "funtp.mm"
include "dmtpop.mm"
include "a1i.mm"
include "df-fn.mm"
include "sylanbrc.mm"

theorem fntp
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cE: class E
  let cF: class F
  assume fntp.1: |- A e. _V
  assume fntp.2: |- B e. _V
  assume fntp.3: |- C e. _V
  assume fntp.4: |- D e. _V
  assume fntp.5: |- E e. _V
  assume fntp.6: |- F e. _V


  assert |- ( ( A =/= B /\ A =/= C /\ B =/= C ) -> { <. A , D >. , <. B , E >. , <. C , F >. } Fn { A , B , C } )

  proof
    cA
    cB
    wne
    cA
    cC
    wne
    cB
    cC
    wne
    w3a
    #
    cA
    cD
    cop
    cB
    cE
    cop
    cC
    cF
    cop
    ctp
    #
    wfun
    @1
    cdm
    cA
    cB
    cC
    ctp
    #
    wceq
    #
    @1
    @2
    wfn
    cA
    cB
    cC
    cD
    cE
    cF
    fntp.1
    fntp.2
    fntp.3
    fntp.4
    fntp.5
    fntp.6
    funtp
    @3
    @0
    cA
    cD
    cB
    cE
    cC
    cF
    fntp.4
    fntp.5
    fntp.6
    dmtpop
    a1i
    @1
    @2
    df-fn
    sylanbrc
end
