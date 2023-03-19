include "cif.mm"
include "wceq.mm"
include "iftrue.mm"
include "syl.mm"

theorem iftrued
  let wph: wff ph
  let wch: wff ch
  let cA: class A
  let cB: class B
  assume iftrued.1: |- ( ph -> ch )


  assert |- ( ph -> if ( ch , A , B ) = A )

  proof
    wph
    wch
    wch
    cA
    cB
    cif
    cA
    wceq
    iftrued.1
    wch
    cA
    cB
    iftrue
    syl
end
