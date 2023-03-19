include "wss.mm"
include "cxr.mm"
include "wa.mm"
include "clt.mm"
include "cinf.mm"
include "cle.mm"
include "wbr.mm"
include "cv.mm"
include "wral.mm"
include "wcel.mm"
include "simplr.mm"
include "simpl.mm"
include "sselda.mm"
include "infxrlb.mm"
include "syl2anc.mm"
include "ralrimiva.mm"
include "wb.mm"
include "sstr.mm"
include "infxrcl.mm"
include "adantl.mm"
include "infxrgelb.mm"
include "mpbird.mm"

theorem infxrss
  let cA: class A
  let cB: class B
  let vx: setvar x


  assert |- ( ( A C_ B /\ B C_ RR* ) -> inf ( B , RR* , < ) <_ inf ( A , RR* , < ) )

  proof
    cA
    cB
    wss
    #
    cB
    cxr
    wss
    #
    wa
    #
    cB
    cxr
    clt
    cinf
    #
    cA
    cxr
    clt
    cinf
    cle
    wbr
    #
    @3
    vx
    cv
    #
    cle
    wbr
    #
    vx
    cA
    wral
    #
    @2
    @6
    vx
    cA
    @2
    @5
    cA
    wcel
    #
    wa
    @1
    @5
    cB
    wcel
    @6
    @0
    @1
    @8
    simplr
    @2
    cA
    cB
    @5
    @0
    @1
    simpl
    sselda
    cB
    @5
    infxrlb
    syl2anc
    ralrimiva
    @2
    cA
    cxr
    wss
    @3
    cxr
    wcel
    #
    @4
    @7
    wb
    cA
    cB
    cxr
    sstr
    @1
    @9
    @0
    cB
    infxrcl
    adantl
    vx
    cA
    @3
    infxrgelb
    syl2anc
    mpbird
end
