include "wceq.mm"
include "cif.mm"
include "ifeq2.mm"
include "syl.mm"

theorem ifeq2d
  let wph: wff ph
  let wps: wff ps
  let cA: class A
  let cB: class B
  let cC: class C
  assume ifeq1d.1: |- ( ph -> A = B )


  assert |- ( ph -> if ( ps , C , A ) = if ( ps , C , B ) )

  proof
    wph
    cA
    cB
    wceq
    wps
    cC
    cA
    cif
    wps
    cC
    cB
    cif
    wceq
    ifeq1d.1
    wps
    cA
    cB
    cC
    ifeq2
    syl
end
