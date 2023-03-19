include "csalg.mm"
include "wcel.mm"
include "cin.mm"
include "salincl.mm"
include "syl3anc.mm"

theorem salincld
  let wph: wff ph
  let cS: class S
  let cE: class E
  let cF: class F
  let vk: setvar k
  let vx: setvar x
  assume salincld.1: |- ( ph -> S e. SAlg )
  assume salincld.2: |- ( ph -> E e. S )
  assume salincld.3: |- ( ph -> F e. S )


  assert |- ( ph -> ( E i^i F ) e. S )

  proof
    wph
    cS
    csalg
    wcel
    cE
    cS
    wcel
    cF
    cS
    wcel
    cE
    cF
    cin
    cS
    wcel
    salincld.1
    salincld.2
    salincld.3
    cS
    cE
    cF
    salincl
    syl3anc
end
