include "cr.mm"
include "wcel.mm"
include "crp.mm"
include "caddc.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "ltaddrp.mm"
include "syl2anc.mm"

theorem ltaddrpd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume rpgecld.1: |- ( ph -> A e. RR )
  assume rpgecld.2: |- ( ph -> B e. RR+ )


  assert |- ( ph -> A < ( A + B ) )

  proof
    wph
    cA
    cr
    wcel
    cB
    crp
    wcel
    cA
    cA
    cB
    caddc
    co
    clt
    wbr
    rpgecld.1
    rpgecld.2
    cA
    cB
    ltaddrp
    syl2anc
end
