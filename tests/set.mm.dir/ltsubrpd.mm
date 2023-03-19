include "cr.mm"
include "wcel.mm"
include "crp.mm"
include "cmin.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "ltsubrp.mm"
include "syl2anc.mm"

theorem ltsubrpd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume rpgecld.1: |- ( ph -> A e. RR )
  assume rpgecld.2: |- ( ph -> B e. RR+ )


  assert |- ( ph -> ( A - B ) < A )

  proof
    wph
    cA
    cr
    wcel
    cB
    crp
    wcel
    cA
    cB
    cmin
    co
    cA
    clt
    wbr
    rpgecld.1
    rpgecld.2
    cA
    cB
    ltsubrp
    syl2anc
end
