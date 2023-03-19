include "cdiv.mm"
include "co.mm"
include "c1.mm"
include "recnd.mm"
include "diveq1bd.mm"
include "eqcomd.mm"

theorem int-mulsimpd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume int-mulsimpd.1: |- ( ph -> B e. RR )
  assume int-mulsimpd.2: |- ( ph -> A = B )
  assume int-mulsimpd.3: |- ( ph -> B =/= 0 )


  assert |- ( ph -> 1 = ( A / B ) )

  proof
    wph
    cA
    cB
    cdiv
    co
    c1
    wph
    cA
    cB
    wph
    cB
    int-mulsimpd.1
    recnd
    int-mulsimpd.3
    int-mulsimpd.2
    diveq1bd
    eqcomd
end
