include "clt.mm"
include "wbr.mm"
include "caddc.mm"
include "co.mm"
include "ltadd2d.mm"
include "mpbid.mm"

theorem ltadd2dd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume ltd.1: |- ( ph -> A e. RR )
  assume ltd.2: |- ( ph -> B e. RR )
  assume letrd.3: |- ( ph -> C e. RR )
  assume ltletrd.4: |- ( ph -> A < B )


  assert |- ( ph -> ( C + A ) < ( C + B ) )

  proof
    wph
    cA
    cB
    clt
    wbr
    cC
    cA
    caddc
    co
    cC
    cB
    caddc
    co
    clt
    wbr
    ltletrd.4
    wph
    cA
    cB
    cC
    ltd.1
    ltd.2
    letrd.3
    ltadd2d
    mpbid
end
