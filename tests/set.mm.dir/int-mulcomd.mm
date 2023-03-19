include "cmul.mm"
include "co.mm"
include "recnd.mm"
include "mulcomd.mm"
include "eqcomd.mm"
include "oveq2d.mm"
include "eqtrd.mm"

theorem int-mulcomd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume int-mulcomd.1: |- ( ph -> B e. RR )
  assume int-mulcomd.2: |- ( ph -> C e. RR )
  assume int-mulcomd.3: |- ( ph -> A = B )


  assert |- ( ph -> ( B x. C ) = ( C x. A ) )

  proof
    wph
    cB
    cC
    cmul
    co
    cC
    cB
    cmul
    co
    cC
    cA
    cmul
    co
    wph
    cB
    cC
    wph
    cB
    int-mulcomd.1
    recnd
    wph
    cC
    int-mulcomd.2
    recnd
    mulcomd
    wph
    cB
    cA
    cC
    cmul
    wph
    cA
    cB
    int-mulcomd.3
    eqcomd
    oveq2d
    eqtrd
end
