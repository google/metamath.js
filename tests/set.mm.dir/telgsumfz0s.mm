include "cc0.mm"
include "cn0.mm"
include "cuz.mm"
include "cfv.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "telgsumfzs.mm"

theorem telgsumfz0s
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cS: class S
  let vi: setvar i
  let vk: setvar k
  let cG: class G
  let c.mi: class .-
  assume telgsumfz0s.b: |- B = ( Base ` G )
  assume telgsumfz0s.g: |- ( ph -> G e. Abel )
  assume telgsumfz0s.m: |- .- = ( -g ` G )
  assume telgsumfz0s.s: |- ( ph -> S e. NN0 )
  assume telgsumfz0s.f: |- ( ph -> A. k e. ( 0 ... ( S + 1 ) ) C e. B )

  disjoint B i
  disjoint B k
  disjoint i k
  disjoint C i
  disjoint G i
  disjoint S i
  disjoint S k
  disjoint .- i
  disjoint i ph
  assert |- ( ph -> ( G gsum ( i e. ( 0 ... S ) |-> ( [_ i / k ]_ C .- [_ ( i + 1 ) / k ]_ C ) ) ) = ( [_ 0 / k ]_ C .- [_ ( S + 1 ) / k ]_ C ) )

  proof
    wph
    cB
    cC
    vi
    vk
    cG
    cc0
    c.mi
    cS
    telgsumfz0s.b
    telgsumfz0s.g
    telgsumfz0s.m
    wph
    cS
    cn0
    cc0
    cuz
    cfv
    telgsumfz0s.s
    nn0uz
    syl6eleq
    telgsumfz0s.f
    telgsumfzs
end
