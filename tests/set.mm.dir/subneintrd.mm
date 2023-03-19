include "cmin.mm"
include "co.mm"
include "wne.mm"
include "subcanad.mm"
include "necon3bid.mm"
include "mpbird.mm"

theorem subneintrd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  assume negidd.1: |- ( ph -> A e. CC )
  assume pncand.2: |- ( ph -> B e. CC )
  assume subaddd.3: |- ( ph -> C e. CC )
  assume subneintrd.4: |- ( ph -> B =/= C )


  assert |- ( ph -> ( A - B ) =/= ( A - C ) )

  proof
    wph
    cA
    cB
    cmin
    co
    #
    cA
    cC
    cmin
    co
    #
    wne
    cB
    cC
    wne
    subneintrd.4
    wph
    @0
    @1
    cB
    cC
    wph
    cA
    cB
    cC
    negidd.1
    pncand.2
    subaddd.3
    subcanad
    necon3bid
    mpbird
end
