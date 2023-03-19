include "wceq.mm"
include "cif.mm"
include "ifeq1.mm"
include "syl.mm"

theorem ifeq1d
  let wph: wff ph
  let wps: wff ps
  let cA: class A
  let cB: class B
  let cC: class C
  assume ifeq1d.1: |- ( ph -> A = B )


  assert |- ( ph -> if ( ps , A , C ) = if ( ps , B , C ) )

  proof
    wph
    cA
    cB
    wceq
    wps
    cA
    cC
    cif
    wps
    cB
    cC
    cif
    wceq
    ifeq1d.1
    wps
    cA
    cB
    cC
    ifeq1
    syl
end
