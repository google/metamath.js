include "cmul.mm"
include "co.mm"
include "cc0.mm"
include "clt.mm"
include "recnd.mm"
include "mulcomd.mm"
include "eqbrtrrd.mm"
include "mul2lt0rgt0.mm"

theorem mul2lt0lgt0
  let wph: wff ph
  let cA: class A
  let cB: class B
  assume mul2lt0.1: |- ( ph -> A e. RR )
  assume mul2lt0.2: |- ( ph -> B e. RR )
  assume mul2lt0.3: |- ( ph -> ( A x. B ) < 0 )


  assert |- ( ( ph /\ 0 < A ) -> B < 0 )

  proof
    wph
    cB
    cA
    mul2lt0.2
    mul2lt0.1
    wph
    cA
    cB
    cmul
    co
    cB
    cA
    cmul
    co
    cc0
    clt
    wph
    cA
    cB
    wph
    cA
    mul2lt0.1
    recnd
    wph
    cB
    mul2lt0.2
    recnd
    mulcomd
    mul2lt0.3
    eqbrtrrd
    mul2lt0rgt0
end
