include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "cdiv.mm"
include "co.mm"
include "c2.mm"
include "cexp.mm"
include "wceq.mm"
include "sqdiv.mm"
include "syl3anc.mm"

theorem sqdivd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume expcld.1: |- ( ph -> A e. CC )
  assume mulexpd.2: |- ( ph -> B e. CC )
  assume sqdivd.3: |- ( ph -> B =/= 0 )


  assert |- ( ph -> ( ( A / B ) ^ 2 ) = ( ( A ^ 2 ) / ( B ^ 2 ) ) )

  proof
    wph
    cA
    cc
    wcel
    cB
    cc
    wcel
    cB
    cc0
    wne
    cA
    cB
    cdiv
    co
    c2
    cexp
    co
    cA
    c2
    cexp
    co
    cB
    c2
    cexp
    co
    cdiv
    co
    wceq
    expcld.1
    mulexpd.2
    sqdivd.3
    cA
    cB
    sqdiv
    syl3anc
end
