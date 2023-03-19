include "caddc.mm"
include "co.mm"
include "clt.mm"
include "ltaddrpd.mm"
include "recnd.mm"
include "rpcnd.mm"
include "addcomd.mm"
include "breqtrd.mm"

theorem ltaddrp2d
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume rpgecld.1: |- ( ph -> A e. RR )
  assume rpgecld.2: |- ( ph -> B e. RR+ )


  assert |- ( ph -> A < ( B + A ) )

  proof
    wph
    cA
    cA
    cB
    caddc
    co
    cB
    cA
    caddc
    co
    clt
    wph
    cA
    cB
    rpgecld.1
    rpgecld.2
    ltaddrpd
    wph
    cA
    cB
    wph
    cA
    rpgecld.1
    recnd
    wph
    cB
    rpgecld.2
    rpcnd
    addcomd
    breqtrd
end
