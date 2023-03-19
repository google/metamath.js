include "cmpt.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "eqid.mm"
include "fmptdf.mm"
include "sge0ge0.mm"

theorem sge0ge0mpt
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cV: class V
  let vx: setvar x
  assume sge0ge0mpt.k: |- F/ k ph
  assume sge0ge0mpt.a: |- ( ph -> A e. V )
  assume sge0ge0mpt.b: |- ( ( ph /\ k e. A ) -> B e. ( 0 [,] +oo ) )

  disjoint A k
  disjoint k x
  assert |- ( ph -> 0 <_ ( sum^ ` ( k e. A |-> B ) ) )

  proof
    wph
    vk
    cA
    cB
    cmpt
    #
    cV
    cA
    sge0ge0mpt.a
    wph
    vk
    cA
    cB
    cc0
    cpnf
    cicc
    co
    @0
    sge0ge0mpt.k
    sge0ge0mpt.b
    @0
    eqid
    fmptdf
    sge0ge0
end
