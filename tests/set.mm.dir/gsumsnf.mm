include "cmnd.mm"
include "wcel.mm"
include "w3a.mm"
include "simp1.mm"
include "simp2.mm"
include "simp3.mm"
include "cv.mm"
include "wceq.mm"
include "adantl.mm"
include "nfv.mm"
include "nfel1.mm"
include "nf3an.mm"
include "gsumsnfd.mm"

theorem gsumsnf
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let cG: class G
  let cM: class M
  let cV: class V
  assume gsumsnf.c: |- F/_ k C
  assume gsumsnf.b: |- B = ( Base ` G )
  assume gsumsnf.s: |- ( k = M -> A = C )

  disjoint B k
  disjoint G k
  disjoint M k
  disjoint V k
  assert |- ( ( G e. Mnd /\ M e. V /\ C e. B ) -> ( G gsum ( k e. { M } |-> A ) ) = C )

  proof
    cG
    cmnd
    wcel
    #
    cM
    cV
    wcel
    #
    cC
    cB
    wcel
    #
    w3a
    #
    cA
    cB
    cC
    vk
    cG
    cM
    cV
    gsumsnf.b
    @0
    @1
    @2
    simp1
    @0
    @1
    @2
    simp2
    @0
    @1
    @2
    simp3
    vk
    cv
    cM
    wceq
    cA
    cC
    wceq
    @3
    gsumsnf.s
    adantl
    @0
    @1
    @2
    vk
    @0
    vk
    nfv
    @1
    vk
    nfv
    vk
    cC
    cB
    gsumsnf.c
    nfel1
    nf3an
    gsumsnf.c
    gsumsnfd
end
