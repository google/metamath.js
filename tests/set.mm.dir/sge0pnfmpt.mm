include "cmpt.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "eqid.mm"
include "fmptdf.mm"
include "cvv.mm"
include "wceq.mm"
include "wrex.mm"
include "eqcom.mm"
include "rexbii.mm"
include "sylib.mm"
include "wcel.mm"
include "pnfex.mm"
include "a1i.mm"
include "elrnmptd.mm"
include "sge0pnfval.mm"

theorem sge0pnfmpt
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cV: class V
  let vx: setvar x
  assume sge0pnfmpt.k: |- F/ k ph
  assume sge0pnfmpt.a: |- ( ph -> A e. V )
  assume sge0pnfmpt.b: |- ( ( ph /\ k e. A ) -> B e. ( 0 [,] +oo ) )
  assume sge0pnfmpt.p: |- ( ph -> E. k e. A B = +oo )

  disjoint A k
  disjoint k x
  assert |- ( ph -> ( sum^ ` ( k e. A |-> B ) ) = +oo )

  proof
    wph
    vk
    cA
    cB
    cmpt
    #
    cV
    cA
    sge0pnfmpt.a
    wph
    vk
    cA
    cB
    cc0
    cpnf
    cicc
    co
    @0
    sge0pnfmpt.k
    sge0pnfmpt.b
    @0
    eqid
    #
    fmptdf
    wph
    vk
    cA
    cB
    cpnf
    @0
    cvv
    @1
    wph
    cB
    cpnf
    wceq
    #
    vk
    cA
    wrex
    cpnf
    cB
    wceq
    #
    vk
    cA
    wrex
    sge0pnfmpt.p
    @2
    @3
    vk
    cA
    cB
    cpnf
    eqcom
    rexbii
    sylib
    cpnf
    cvv
    wcel
    wph
    pnfex
    a1i
    elrnmptd
    sge0pnfval
end
