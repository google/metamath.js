include "cnp.mm"
include "wcel.mm"
include "wa.mm"
include "cop.mm"
include "cer.mm"
include "wbr.mm"
include "cec.mm"
include "wceq.mm"
include "cpp.mm"
include "co.mm"
include "cxp.mm"
include "wer.mm"
include "enrer.mm"
include "a1i.mm"
include "opelxpi.mm"
include "adantr.mm"
include "erth.mm"
include "enrbreq.mm"
include "bitr3d.mm"

theorem enreceq
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D


  assert |- ( ( ( A e. P. /\ B e. P. ) /\ ( C e. P. /\ D e. P. ) ) -> ( [ <. A , B >. ] ~R = [ <. C , D >. ] ~R <-> ( A +P. D ) = ( B +P. C ) ) )

  proof
    cA
    cnp
    wcel
    cB
    cnp
    wcel
    wa
    #
    cC
    cnp
    wcel
    cD
    cnp
    wcel
    wa
    #
    wa
    #
    cA
    cB
    cop
    #
    cC
    cD
    cop
    #
    cer
    wbr
    @3
    cer
    cec
    @4
    cer
    cec
    wceq
    cA
    cD
    cpp
    co
    cB
    cC
    cpp
    co
    wceq
    @2
    @3
    @4
    cer
    cnp
    cnp
    cxp
    #
    @5
    cer
    wer
    @2
    enrer
    a1i
    @0
    @3
    @5
    wcel
    @1
    cA
    cB
    cnp
    cnp
    opelxpi
    adantr
    erth
    cA
    cB
    cC
    cD
    enrbreq
    bitr3d
end
