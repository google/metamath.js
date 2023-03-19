include "cn.mm"
include "wcel.mm"
include "w3a.mm"
include "sseli.mm"
include "3anim123i.mm"
include "3ad2ant3.mm"
include "syl2anc.mm"

theorem nnssi3
  let wph: wff ph
  let wps: wff ps
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  assume nnssi3.1: |- NN C_ D
  assume nnssi3.2: |- ( C e. NN -> ph )
  assume nnssi3.3: |- ( ( ( A e. D /\ B e. D /\ C e. D ) /\ ph ) -> ps )


  assert |- ( ( A e. NN /\ B e. NN /\ C e. NN ) -> ps )

  proof
    cA
    cn
    wcel
    #
    cB
    cn
    wcel
    #
    cC
    cn
    wcel
    #
    w3a
    cA
    cD
    wcel
    #
    cB
    cD
    wcel
    #
    cC
    cD
    wcel
    #
    w3a
    wph
    wps
    @0
    @3
    @1
    @4
    @2
    @5
    cn
    cD
    cA
    nnssi3.1
    sseli
    cn
    cD
    cB
    nnssi3.1
    sseli
    cn
    cD
    cC
    nnssi3.1
    sseli
    3anim123i
    @2
    @0
    wph
    @1
    nnssi3.2
    3ad2ant3
    nnssi3.3
    syl2anc
end
