include "cmin.mm"
include "co.mm"
include "cc0.mm"
include "wne.mm"
include "cc.mm"
include "wcel.mm"
include "wceq.mm"
include "wb.mm"
include "subeq0.mm"
include "syl2anc.mm"
include "necon3bid.mm"
include "mpbird.mm"

theorem subne0d
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume negidd.1: |- ( ph -> A e. CC )
  assume pncand.2: |- ( ph -> B e. CC )
  assume subne0d.3: |- ( ph -> A =/= B )


  assert |- ( ph -> ( A - B ) =/= 0 )

  proof
    wph
    cA
    cB
    cmin
    co
    #
    cc0
    wne
    cA
    cB
    wne
    subne0d.3
    wph
    @0
    cc0
    cA
    cB
    wph
    cA
    cc
    wcel
    cB
    cc
    wcel
    @0
    cc0
    wceq
    cA
    cB
    wceq
    wb
    negidd.1
    pncand.2
    cA
    cB
    subeq0
    syl2anc
    necon3bid
    mpbird
end
