include "ifbieq12d.mm"

theorem ifeq123d
  let wph: wff ph
  let wps: wff ps
  let wch: wff ch
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume ifeq123d.1: |- ( ph -> ( ps <-> ch ) )
  assume ifeq123d.2: |- ( ph -> A = B )
  assume ifeq123d.3: |- ( ph -> C = D )


  assert |- ( ph -> if ( ps , A , C ) = if ( ch , B , D ) )

  proof
    wph
    wps
    wch
    cA
    cC
    cB
    cD
    ifeq123d.1
    ifeq123d.2
    ifeq123d.3
    ifbieq12d
end
