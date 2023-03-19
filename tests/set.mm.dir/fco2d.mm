include "cres.mm"
include "wf.mm"
include "ccom.mm"
include "wa.mm"
include "wi.mm"
include "fco2.mm"
include "a1i.mm"
include "mp2and.mm"

theorem fco2d
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cF: class F
  let cG: class G
  assume fco2d.1: |- ( ph -> G : A --> B )
  assume fco2d.2: |- ( ph -> ( F |` B ) : B --> C )


  assert |- ( ph -> ( F o. G ) : A --> C )

  proof
    wph
    cB
    cC
    cF
    cB
    cres
    wf
    #
    cA
    cB
    cG
    wf
    #
    cA
    cC
    cF
    cG
    ccom
    wf
    #
    fco2d.2
    fco2d.1
    @0
    @1
    wa
    @2
    wi
    wph
    cA
    cB
    cC
    cF
    cG
    fco2
    a1i
    mp2and
end
