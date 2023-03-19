include "wcel.mm"
include "clsp.mm"
include "cfv.mm"
include "crn.mm"
include "cxr.mm"
include "clt.mm"
include "cinf.mm"
include "wceq.mm"
include "limsupval.mm"
include "syl.mm"

theorem limsupvald
  let wph: wff ph
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cV: class V
  let vx: setvar x
  assume limsupvald.1: |- ( ph -> F e. V )
  assume limsupvald.2: |- G = ( k e. RR |-> sup ( ( ( F " ( k [,) +oo ) ) i^i RR* ) , RR* , < ) )

  disjoint F k
  disjoint k x
  assert |- ( ph -> ( limsup ` F ) = inf ( ran G , RR* , < ) )

  proof
    wph
    cF
    cV
    wcel
    cF
    clsp
    cfv
    cG
    crn
    cxr
    clt
    cinf
    wceq
    limsupvald.1
    vk
    cF
    cG
    cV
    limsupvald.2
    limsupval
    syl
end
