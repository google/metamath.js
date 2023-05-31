include "wceq.mm"
include "cif.mm"
include "ifeq1.mm"
include "syl.mm"

theorem ifeq1d
  param wph: wff ph
  param wps: wff ps
  param cA: class A
  param cB: class B
  param cC: class C
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
