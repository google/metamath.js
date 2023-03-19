include "cn.mm"
include "wcel.mm"
include "wa.mm"
include "w3a.mm"
include "sseli.mm"
include "3anim123i.mm"
include "3anidm23.mm"
include "syl.mm"

theorem nnssi2
  let wph: wff ph
  let wps: wff ps
  let cA: class A
  let cB: class B
  let cD: class D
  assume nnssi2.1: |- NN C_ D
  assume nnssi2.2: |- ( B e. NN -> ph )
  assume nnssi2.3: |- ( ( A e. D /\ B e. D /\ ph ) -> ps )


  assert |- ( ( A e. NN /\ B e. NN ) -> ps )

  proof
    cA
    cn
    wcel
    #
    cB
    cn
    wcel
    #
    wa
    cA
    cD
    wcel
    #
    cB
    cD
    wcel
    #
    wph
    w3a
    #
    wps
    @0
    @1
    @4
    @0
    @2
    @1
    @3
    @1
    wph
    cn
    cD
    cA
    nnssi2.1
    sseli
    cn
    cD
    cB
    nnssi2.1
    sseli
    nnssi2.2
    3anim123i
    3anidm23
    nnssi2.3
    syl
end
