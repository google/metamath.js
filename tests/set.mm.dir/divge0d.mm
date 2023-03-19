include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "clt.mm"
include "wa.mm"
include "cdiv.mm"
include "co.mm"
include "rpregt0d.mm"
include "divge0.mm"
include "syl21anc.mm"

theorem divge0d
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume rpgecld.1: |- ( ph -> A e. RR )
  assume rpgecld.2: |- ( ph -> B e. RR+ )
  assume divge0d.3: |- ( ph -> 0 <_ A )


  assert |- ( ph -> 0 <_ ( A / B ) )

  proof
    wph
    cA
    cr
    wcel
    cc0
    cA
    cle
    wbr
    cB
    cr
    wcel
    cc0
    cB
    clt
    wbr
    wa
    cc0
    cA
    cB
    cdiv
    co
    cle
    wbr
    rpgecld.1
    divge0d.3
    wph
    cB
    rpgecld.2
    rpregt0d
    cA
    cB
    divge0
    syl21anc
end
