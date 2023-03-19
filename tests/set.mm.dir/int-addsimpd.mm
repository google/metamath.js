include "cmin.mm"
include "co.mm"
include "cc0.mm"
include "recnd.mm"
include "subeq0bd.mm"
include "eqcomd.mm"

theorem int-addsimpd
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume int-addsimpd.1: |- ( ph -> A e. RR )
  assume int-addsimpd.2: |- ( ph -> A = B )


  assert |- ( ph -> 0 = ( A - B ) )

  proof
    wph
    cA
    cB
    cmin
    co
    cc0
    wph
    cA
    cB
    wph
    cA
    int-addsimpd.1
    recnd
    int-addsimpd.2
    subeq0bd
    eqcomd
end
