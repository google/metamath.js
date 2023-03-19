include "csalg.mm"
include "wcel.mm"
include "cun.mm"
include "saluncl.mm"
include "syl3anc.mm"

theorem saluncld
  let wph: wff ph
  let cS: class S
  let cE: class E
  let cF: class F
  let vk: setvar k
  let vx: setvar x
  assume saluncld.1: |- ( ph -> S e. SAlg )
  assume saluncld.2: |- ( ph -> E e. S )
  assume saluncld.3: |- ( ph -> F e. S )


  assert |- ( ph -> ( E u. F ) e. S )

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
    cun
    cS
    wcel
    saluncld.1
    saluncld.2
    saluncld.3
    cS
    cE
    cF
    saluncl
    syl3anc
end
