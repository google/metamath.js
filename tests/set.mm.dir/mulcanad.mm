include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "mulcand.mm"
include "mpbid.mm"

theorem mulcanad
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume mulcanad.1: |- ( ph -> A e. CC )
  assume mulcanad.2: |- ( ph -> B e. CC )
  assume mulcanad.3: |- ( ph -> C e. CC )
  assume mulcanad.4: |- ( ph -> C =/= 0 )
  assume mulcanad.5: |- ( ph -> ( C x. A ) = ( C x. B ) )


  assert |- ( ph -> A = B )

  proof
    wph
    cC
    cA
    cmul
    co
    cC
    cB
    cmul
    co
    wceq
    cA
    cB
    wceq
    mulcanad.5
    wph
    cA
    cB
    cC
    mulcanad.1
    mulcanad.2
    mulcanad.3
    mulcanad.4
    mulcand
    mpbid
end
