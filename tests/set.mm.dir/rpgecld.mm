include "crp.mm"
include "wcel.mm"
include "cr.mm"
include "cle.mm"
include "wbr.mm"
include "rpgecl.mm"
include "syl3anc.mm"

theorem rpgecld
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume rpgecld.1: |- ( ph -> A e. RR )
  assume rpgecld.2: |- ( ph -> B e. RR+ )
  assume rpgecld.3: |- ( ph -> B <_ A )


  assert |- ( ph -> A e. RR+ )

  proof
    wph
    cB
    crp
    wcel
    cA
    cr
    wcel
    cB
    cA
    cle
    wbr
    cA
    crp
    wcel
    rpgecld.2
    rpgecld.1
    rpgecld.3
    cB
    cA
    rpgecl
    syl3anc
end
