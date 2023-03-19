include "cgrcomrand.mm"
include "cgrcomland.mm"

theorem cgrcomlrand
  let wph: wff ph
  let wps: wff ps
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cN: class N
  assume cgrcomlrand.1: |- ( ph -> N e. NN )
  assume cgrcomlrand.2: |- ( ph -> A e. ( EE ` N ) )
  assume cgrcomlrand.3: |- ( ph -> B e. ( EE ` N ) )
  assume cgrcomlrand.4: |- ( ph -> C e. ( EE ` N ) )
  assume cgrcomlrand.5: |- ( ph -> D e. ( EE ` N ) )
  assume cgrcomlrand.6: |- ( ( ph /\ ps ) -> <. A , B >. Cgr <. C , D >. )


  assert |- ( ( ph /\ ps ) -> <. B , A >. Cgr <. D , C >. )

  proof
    wph
    wps
    cA
    cB
    cD
    cC
    cN
    cgrcomlrand.1
    cgrcomlrand.2
    cgrcomlrand.3
    cgrcomlrand.5
    cgrcomlrand.4
    wph
    wps
    cA
    cB
    cC
    cD
    cN
    cgrcomlrand.1
    cgrcomlrand.2
    cgrcomlrand.3
    cgrcomlrand.4
    cgrcomlrand.5
    cgrcomlrand.6
    cgrcomrand
    cgrcomland
end
