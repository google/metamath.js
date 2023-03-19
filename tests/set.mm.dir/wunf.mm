include "cmap.mm"
include "co.mm"
include "wunmap.mm"
include "wunelss.mm"
include "wcel.mm"
include "wf.mm"
include "elmapd.mm"
include "mpbird.mm"
include "sseldd.mm"

theorem wunf
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cU: class U
  let cF: class F
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume wun0.1: |- ( ph -> U e. WUni )
  assume wunop.2: |- ( ph -> A e. U )
  assume wunop.3: |- ( ph -> B e. U )
  assume wunf.3: |- ( ph -> F : A --> B )


  assert |- ( ph -> F e. U )

  proof
    wph
    cB
    cA
    cmap
    co
    #
    cU
    cF
    wph
    @0
    cU
    wun0.1
    wph
    cB
    cA
    cU
    wun0.1
    wunop.3
    wunop.2
    wunmap
    wunelss
    wph
    cF
    @0
    wcel
    cA
    cB
    cF
    wf
    wunf.3
    wph
    cB
    cA
    cF
    cU
    cU
    wunop.3
    wunop.2
    elmapd
    mpbird
    sseldd
end
