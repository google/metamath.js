include "wss.mm"
include "cxr.mm"
include "wa.mm"
include "clt.mm"
include "csup.mm"
include "cle.mm"
include "wbr.mm"
include "cv.mm"
include "wral.mm"
include "wcel.mm"
include "simplr.mm"
include "simpl.mm"
include "sselda.mm"
include "supxrub.mm"
include "syl2anc.mm"
include "ralrimiva.mm"
include "wb.mm"
include "sstr.mm"
include "supxrcl.mm"
include "adantl.mm"
include "supxrleub.mm"
include "mpbird.mm"

theorem supxrss
  let cA: class A
  let cB: class B
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w


  assert |- ( ( A C_ B /\ B C_ RR* ) -> sup ( A , RR* , < ) <_ sup ( B , RR* , < ) )

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
    cA
    cxr
    clt
    csup
    cB
    cxr
    clt
    csup
    #
    cle
    wbr
    #
    vx
    cv
    #
    @3
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
    supxrub
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
    supxrcl
    adantl
    vx
    cA
    @3
    supxrleub
    syl2anc
    mpbird
end
