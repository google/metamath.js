include "wpss.mm"
include "wn.mm"
include "wi.mm"
include "wa.mm"
include "wss.mm"
include "dfpss3.mm"
include "simprbi.mm"
include "pssss.mm"
include "nsyl.mm"
include "imnan.mm"
include "mpbi.mm"

theorem pssn2lp
  let cA: class A
  let cB: class B


  assert |- -. ( A C. B /\ B C. A )

  proof
    cA
    cB
    wpss
    #
    cB
    cA
    wpss
    #
    wn
    wi
    @0
    @1
    wa
    wn
    @0
    cB
    cA
    wss
    #
    @1
    @0
    cA
    cB
    wss
    @2
    wn
    cA
    cB
    dfpss3
    simprbi
    cB
    cA
    pssss
    nsyl
    @0
    @1
    imnan
    mpbi
end
