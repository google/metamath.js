include "wcel.mm"
include "cif.mm"
include "ifcl.mm"
include "syl2anc.mm"

theorem ifcld
  let wph: wff ph
  let wps: wff ps
  let cA: class A
  let cB: class B
  let cC: class C
  assume ifcld.a: |- ( ph -> A e. C )
  assume ifcld.b: |- ( ph -> B e. C )


  assert |- ( ph -> if ( ps , A , B ) e. C )

  proof
    wph
    cA
    cC
    wcel
    cB
    cC
    wcel
    wps
    cA
    cB
    cif
    cC
    wcel
    ifcld.a
    ifcld.b
    wps
    cA
    cB
    cC
    ifcl
    syl2anc
end
