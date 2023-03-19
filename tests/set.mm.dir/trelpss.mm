include "wtr.mm"
include "wcel.mm"
include "wa.mm"
include "wss.mm"
include "wne.mm"
include "wpss.mm"
include "cep.mm"
include "wfr.mm"
include "zfregfr.mm"
include "tz7.2.mm"
include "mp3an2.mm"
include "df-pss.mm"
include "sylibr.mm"

theorem trelpss
  let cA: class A
  let cB: class B


  assert |- ( ( Tr A /\ B e. A ) -> B C. A )

  proof
    cA
    wtr
    #
    cB
    cA
    wcel
    #
    wa
    cB
    cA
    wss
    cB
    cA
    wne
    wa
    #
    cB
    cA
    wpss
    @0
    cA
    cep
    wfr
    @1
    @2
    cA
    zfregfr
    cA
    cB
    tz7.2
    mp3an2
    cB
    cA
    df-pss
    sylibr
end
