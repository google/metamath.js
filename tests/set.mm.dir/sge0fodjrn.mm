include "ccnv.mm"
include "c0.mm"
include "csn.mm"
include "cima.mm"
include "eqid.mm"
include "sge0fodjrnlem.mm"

theorem sge0fodjrn
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vk: setvar k
  let vn: setvar n
  let cF: class F
  let cG: class G
  let cV: class V
  let vx: setvar x
  assume sge0fodjrn.k: |- F/ k ph
  assume sge0fodjrn.n: |- F/ n ph
  assume sge0fodjrn.bd: |- ( k = G -> B = D )
  assume sge0fodjrn.c: |- ( ph -> C e. V )
  assume sge0fodjrn.f: |- ( ph -> F : C -onto-> A )
  assume sge0fodjrn.dj: |- ( ph -> Disj_ n e. C ( F ` n ) )
  assume sge0fodjrn.fng: |- ( ( ph /\ n e. C ) -> ( F ` n ) = G )
  assume sge0fodjrn.b: |- ( ( ph /\ k e. A ) -> B e. ( 0 [,] +oo ) )
  assume sge0fodjrn.b0: |- ( ( ph /\ k = (/) ) -> B = 0 )

  disjoint A k
  disjoint A n
  disjoint k n
  disjoint B n
  disjoint C k
  disjoint C n
  disjoint D k
  disjoint F k
  disjoint F n
  disjoint G k
  disjoint k x
  assert |- ( ph -> ( sum^ ` ( k e. A |-> B ) ) = ( sum^ ` ( n e. C |-> D ) ) )

  proof
    wph
    cA
    cB
    cC
    cD
    vk
    vn
    cF
    cG
    cV
    cF
    ccnv
    c0
    csn
    cima
    #
    sge0fodjrn.k
    sge0fodjrn.n
    sge0fodjrn.bd
    sge0fodjrn.c
    sge0fodjrn.f
    sge0fodjrn.dj
    sge0fodjrn.fng
    sge0fodjrn.b
    sge0fodjrn.b0
    @0
    eqid
    sge0fodjrnlem
end
