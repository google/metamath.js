include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "cz.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cexp.mm"
include "cmul.mm"
include "wceq.mm"
include "expp1z.mm"
include "syl3anc.mm"

theorem expp1zd
  let wph: wff ph
  let cA: class A
  let cN: class N
  assume expcld.1: |- ( ph -> A e. CC )
  assume sqrecd.1: |- ( ph -> A =/= 0 )
  assume expclzd.3: |- ( ph -> N e. ZZ )


  assert |- ( ph -> ( A ^ ( N + 1 ) ) = ( ( A ^ N ) x. A ) )

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
    cA
    cN
    c1
    caddc
    co
    cexp
    co
    cA
    cN
    cexp
    co
    cA
    cmul
    co
    wceq
    expcld.1
    sqrecd.1
    expclzd.3
    cA
    cN
    expp1z
    syl3anc
end
