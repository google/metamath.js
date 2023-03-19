include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "cz.mm"
include "c1.mm"
include "cdiv.mm"
include "co.mm"
include "cexp.mm"
include "wceq.mm"
include "exprec.mm"
include "syl3anc.mm"

theorem exprecd
  let wph: wff ph
  let cA: class A
  let cN: class N
  assume expcld.1: |- ( ph -> A e. CC )
  assume sqrecd.1: |- ( ph -> A =/= 0 )
  assume expclzd.3: |- ( ph -> N e. ZZ )


  assert |- ( ph -> ( ( 1 / A ) ^ N ) = ( 1 / ( A ^ N ) ) )

  proof
    wph
    cA
    cc
    wcel
    cA
    cc0
    wne
    cN
    cz
    wcel
    c1
    cA
    cdiv
    co
    cN
    cexp
    co
    c1
    cA
    cN
    cexp
    co
    cdiv
    co
    wceq
    expcld.1
    sqrecd.1
    expclzd.3
    cA
    cN
    exprec
    syl3anc
end
