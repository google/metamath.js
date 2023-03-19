include "wn.mm"
include "cif.mm"
include "wceq.mm"
include "iffalse.mm"
include "syl.mm"

theorem iffalsed
  let wph: wff ph
  let wch: wff ch
  let cA: class A
  let cB: class B
  assume iffalsed.1: |- ( ph -> -. ch )


  assert |- ( ph -> if ( ch , A , B ) = B )

  proof
    wph
    wch
    wn
    wch
    cA
    cB
    cif
    cB
    wceq
    iffalsed.1
    wch
    cA
    cB
    iffalse
    syl
end
