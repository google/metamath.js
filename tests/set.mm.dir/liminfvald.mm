include "wcel.mm"
include "clsi.mm"
include "cfv.mm"
include "crn.mm"
include "cxr.mm"
include "clt.mm"
include "csup.mm"
include "wceq.mm"
include "liminfval.mm"
include "syl.mm"

theorem liminfvald
  let wph: wff ph
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cV: class V
  let vx: setvar x
  assume liminfvald.1: |- ( ph -> F e. V )
  assume liminfvald.2: |- G = ( k e. RR |-> inf ( ( ( F " ( k [,) +oo ) ) i^i RR* ) , RR* , < ) )

  disjoint F k
  disjoint k x
  assert |- ( ph -> ( liminf ` F ) = sup ( ran G , RR* , < ) )

  proof
    wph
    cF
    cV
    wcel
    cF
    clsi
    cfv
    cG
    crn
    cxr
    clt
    csup
    wceq
    liminfvald.1
    vk
    cF
    cG
    cV
    liminfvald.2
    liminfval
    syl
end
