include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "mulcan2d.mm"
include "mpbid.mm"

theorem mulcan2ad
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume mulcanad.1: |- ( ph -> A e. CC )
  assume mulcanad.2: |- ( ph -> B e. CC )
  assume mulcanad.3: |- ( ph -> C e. CC )
  assume mulcanad.4: |- ( ph -> C =/= 0 )
  assume mulcan2ad.5: |- ( ph -> ( A x. C ) = ( B x. C ) )


  assert |- ( ph -> A = B )

  proof
    wph
    cA
    cC
    cmul
    co
    cB
    cC
    cmul
    co
    wceq
    cA
    cB
    wceq
    mulcan2ad.5
    wph
    cA
    cB
    cC
    mulcanad.1
    mulcanad.2
    mulcanad.3
    mulcanad.4
    mulcan2d
    mpbid
end
