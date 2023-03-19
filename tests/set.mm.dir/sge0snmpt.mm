include "csn.mm"
include "cmpt.mm"
include "csumge0.mm"
include "cfv.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "elsni.mm"
include "syl.mm"
include "adantl.mm"
include "adantr.mm"
include "eqeltrd.mm"
include "eqid.mm"
include "fmptd.mm"
include "sge0sn.mm"
include "eqidd.mm"
include "snidg.mm"
include "fvmptd.mm"
include "eqtrd.mm"

theorem sge0snmpt
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let cV: class V
  let vx: setvar x
  assume sge0snmpt.a: |- ( ph -> A e. V )
  assume sge0snmpt.c: |- ( ph -> C e. ( 0 [,] +oo ) )
  assume sge0snmpt.b: |- ( k = A -> B = C )

  disjoint A k
  disjoint C k
  disjoint k ph
  disjoint k x
  assert |- ( ph -> ( sum^ ` ( k e. { A } |-> B ) ) = C )

  proof
    wph
    vk
    cA
    csn
    #
    cB
    cmpt
    #
    csumge0
    cfv
    cA
    @1
    cfv
    cC
    wph
    cA
    @1
    cV
    sge0snmpt.a
    wph
    vk
    @0
    cB
    cc0
    cpnf
    cicc
    co
    #
    @1
    wph
    vk
    cv
    #
    @0
    wcel
    #
    wa
    cB
    cC
    @2
    @4
    cB
    cC
    wceq
    #
    wph
    @4
    @3
    cA
    wceq
    #
    @5
    @3
    cA
    elsni
    sge0snmpt.b
    syl
    adantl
    wph
    cC
    @2
    wcel
    @4
    sge0snmpt.c
    adantr
    eqeltrd
    @1
    eqid
    fmptd
    sge0sn
    wph
    vk
    cA
    cB
    cC
    @0
    @1
    @2
    wph
    @1
    eqidd
    @6
    @5
    wph
    sge0snmpt.b
    adantl
    wph
    cA
    cV
    wcel
    cA
    @0
    wcel
    sge0snmpt.a
    cA
    cV
    snidg
    syl
    sge0snmpt.c
    fvmptd
    eqtrd
end
