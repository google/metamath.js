include "keepel.mm"

theorem ifcli
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume ifcli.1: |- A e. C
  assume ifcli.2: |- B e. C


  assert |- if ( ph , A , B ) e. C

  proof
    wph
    cA
    cB
    cC
    ifcli.1
    ifcli.2
    keepel
end
