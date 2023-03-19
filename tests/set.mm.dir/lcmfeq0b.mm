include "cz.mm"
include "wss.mm"
include "cfn.mm"
include "wcel.mm"
include "wa.mm"
include "clcmf.mm"
include "cfv.mm"
include "cc0.mm"
include "wceq.mm"
include "wn.mm"
include "wnel.mm"
include "wne.mm"
include "df-nel.mm"
include "w3a.mm"
include "lcmfn0cl.mm"
include "nnne0d.mm"
include "3expia.mm"
include "syl5bir.mm"
include "necon4bd.mm"
include "wi.mm"
include "lcmf0val.mm"
include "ex.mm"
include "adantr.mm"
include "impbid.mm"

theorem lcmfeq0b
  let cZ: class Z


  assert |- ( ( Z C_ ZZ /\ Z e. Fin ) -> ( ( _lcm ` Z ) = 0 <-> 0 e. Z ) )

  proof
    cZ
    cz
    wss
    #
    cZ
    cfn
    wcel
    #
    wa
    #
    cZ
    clcmf
    cfv
    #
    cc0
    wceq
    #
    cc0
    cZ
    wcel
    #
    @2
    @5
    @3
    cc0
    @5
    wn
    cc0
    cZ
    wnel
    #
    @2
    @3
    cc0
    wne
    #
    cc0
    cZ
    df-nel
    @0
    @1
    @6
    @7
    @0
    @1
    @6
    w3a
    @3
    cZ
    lcmfn0cl
    nnne0d
    3expia
    syl5bir
    necon4bd
    @0
    @5
    @4
    wi
    @1
    @0
    @5
    @4
    cZ
    lcmf0val
    ex
    adantr
    impbid
end
