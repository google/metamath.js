include "cdiv.mm"
include "co.mm"
include "c1.mm"
include "wceq.mm"
include "cc.mm"
include "wcel.mm"
include "cc0.mm"
include "wne.mm"
include "wb.mm"
include "diveq1.mm"
include "syl3anc.mm"
include "mpbid.mm"

theorem diveq1d
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume div1d.1: |- ( ph -> A e. CC )
  assume divcld.2: |- ( ph -> B e. CC )
  assume divcld.3: |- ( ph -> B =/= 0 )
  assume diveq1d.4: |- ( ph -> ( A / B ) = 1 )


  assert |- ( ph -> A = B )

  proof
    wph
    cA
    cB
    cdiv
    co
    c1
    wceq
    #
    cA
    cB
    wceq
    #
    diveq1d.4
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
    @0
    @1
    wb
    div1d.1
    divcld.2
    divcld.3
    cA
    cB
    diveq1
    syl3anc
    mpbid
end
