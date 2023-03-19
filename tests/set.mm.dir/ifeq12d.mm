include "cif.mm"
include "ifeq1d.mm"
include "ifeq2d.mm"
include "eqtrd.mm"

theorem ifeq12d
  let wph: wff ph
  let wps: wff ps
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume ifeq1d.1: |- ( ph -> A = B )
  assume ifeq12d.2: |- ( ph -> C = D )


  assert |- ( ph -> if ( ps , A , C ) = if ( ps , B , D ) )

  proof
    wph
    wps
    cA
    cC
    cif
    wps
    cB
    cC
    cif
    wps
    cB
    cD
    cif
    wph
    wps
    cA
    cB
    cC
    ifeq1d.1
    ifeq1d
    wph
    wps
    cC
    cD
    cB
    ifeq12d.2
    ifeq2d
    eqtrd
end
