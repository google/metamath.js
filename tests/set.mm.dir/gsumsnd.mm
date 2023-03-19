include "nfv.mm"
include "nfcv.mm"
include "gsumsnfd.mm"

theorem gsumsnd
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let cG: class G
  let cM: class M
  let cV: class V
  assume gsumsnd.b: |- B = ( Base ` G )
  assume gsumsnd.g: |- ( ph -> G e. Mnd )
  assume gsumsnd.m: |- ( ph -> M e. V )
  assume gsumsnd.c: |- ( ph -> C e. B )
  assume gsumsnd.s: |- ( ( ph /\ k = M ) -> A = C )

  disjoint M k
  disjoint C k
  disjoint k ph
  assert |- ( ph -> ( G gsum ( k e. { M } |-> A ) ) = C )

  proof
    wph
    cA
    cB
    cC
    vk
    cG
    cM
    cV
    gsumsnd.b
    gsumsnd.g
    gsumsnd.m
    gsumsnd.c
    gsumsnd.s
    wph
    vk
    nfv
    vk
    cC
    nfcv
    gsumsnfd
end
