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
include "fmptdf.mm"
include "sge0sn.mm"
include "snidg.mm"
include "fvmptg.mm"
include "syl2anc.mm"
include "eqtrd.mm"

theorem sge0snmptf
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let vk: setvar k
  let cV: class V
  let vx: setvar x
  assume sge0snmptf.k: |- F/ k ph
  assume sge0snmptf.a: |- ( ph -> A e. V )
  assume sge0snmptf.c: |- ( ph -> C e. ( 0 [,] +oo ) )
  assume sge0snmptf.b: |- ( k = A -> B = C )

  disjoint A k
  disjoint C k
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
    #
    cC
    wph
    cA
    @1
    cV
    sge0snmptf.a
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
    sge0snmptf.k
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
    @3
    @5
    cB
    cC
    wceq
    #
    wph
    @5
    @4
    cA
    wceq
    @6
    @4
    cA
    elsni
    sge0snmptf.b
    syl
    adantl
    wph
    cC
    @3
    wcel
    #
    @5
    sge0snmptf.c
    adantr
    eqeltrd
    @1
    eqid
    #
    fmptdf
    sge0sn
    wph
    cA
    @0
    wcel
    #
    @7
    @2
    cC
    wceq
    wph
    cA
    cV
    wcel
    @9
    sge0snmptf.a
    cA
    cV
    snidg
    syl
    sge0snmptf.c
    vk
    cA
    cB
    cC
    @0
    @3
    @1
    sge0snmptf.b
    @8
    fvmptg
    syl2anc
    eqtrd
end
