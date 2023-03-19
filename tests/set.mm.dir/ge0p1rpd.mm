include "cr.mm"
include "wcel.mm"
include "cc0.mm"
include "cle.mm"
include "wbr.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "crp.mm"
include "ge0p1rp.mm"
include "syl2anc.mm"

theorem ge0p1rpd
  let wph: wff ph
  let cA: class A
  assume rpgecld.1: |- ( ph -> A e. RR )
  assume ge0p1rp.2: |- ( ph -> 0 <_ A )


  assert |- ( ph -> ( A + 1 ) e. RR+ )

  proof
    wph
    cA
    cr
    wcel
    cc0
    cA
    cle
    wbr
    cA
    c1
    caddc
    co
    crp
    wcel
    rpgecld.1
    ge0p1rp.2
    cA
    ge0p1rp
    syl2anc
end
