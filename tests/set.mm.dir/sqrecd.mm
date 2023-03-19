include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "c2.mm"
include "cz.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "cexp.mm"
include "wceq.mm"
include "2z.mm"
include "a1i.mm"
include "exprec.mm"
include "syl3anc.mm"

theorem sqrecd
  let wph: wff ph
  let cA: class A
  assume expcld.1: |- ( ph -> A e. CC )
  assume sqrecd.1: |- ( ph -> A =/= 0 )


  assert |- ( ph -> ( ( 1 / A ) ^ 2 ) = ( 1 / ( A ^ 2 ) ) )

  proof
    wph
    cA
    cc
    wcel
    cA
    cc0
    wne
    c2
    cz
    wcel
    #
    c1
    cA
    cdiv
    co
    c2
    cexp
    co
    c1
    cA
    c2
    cexp
    co
    cdiv
    co
    wceq
    expcld.1
    sqrecd.1
    @0
    wph
    2z
    a1i
    cA
    c2
    exprec
    syl3anc
end
