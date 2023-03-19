include "casa.mm"
include "wcel.mm"
include "clmod.mm"
include "assalmod.mm"
include "syl.mm"
include "crg.mm"
include "assaring.mm"
include "ascl1.mm"

theorem assaascl1
  let wph: wff ph
  let cA: class A
  let cF: class F
  let cW: class W
  let vk: setvar k
  let vx: setvar x
  assume ascl0.a: |- A = ( algSc ` W )
  assume ascl0.f: |- F = ( Scalar ` W )
  assume assaascl0.a: |- ( ph -> W e. AssAlg )


  assert |- ( ph -> ( A ` ( 1r ` F ) ) = ( 1r ` W ) )

  proof
    wph
    cA
    cF
    cW
    ascl0.a
    ascl0.f
    wph
    cW
    casa
    wcel
    #
    cW
    clmod
    wcel
    assaascl0.a
    cW
    assalmod
    syl
    wph
    @0
    cW
    crg
    wcel
    assaascl0.a
    cW
    assaring
    syl
    ascl1
end
