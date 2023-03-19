include "csn.mm"
include "cun.mm"
include "cmpt.mm"
include "csumge0.mm"
include "cfv.mm"
include "cxad.mm"
include "co.mm"
include "cvv.mm"
include "cfn.mm"
include "wcel.mm"
include "snfi.mm"
include "a1i.mm"
include "elexd.mm"
include "wn.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "disjsn.mm"
include "sylibr.mm"
include "cv.mm"
include "wa.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "elsni.mm"
include "adantl.mm"
include "sylan2.mm"
include "adantr.mm"
include "eqeltrd.mm"
include "sge0splitmpt.mm"
include "sge0snmptf.mm"
include "oveq2d.mm"
include "eqtrd.mm"

theorem sge0splitsn
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vk: setvar k
  let cV: class V
  let cW: class W
  let vx: setvar x
  assume sge0splitsn.ph: |- F/ k ph
  assume sge0splitsn.a: |- ( ph -> A e. V )
  assume sge0splitsn.b: |- ( ph -> B e. W )
  assume sge0splitsn.n: |- ( ph -> -. B e. A )
  assume sge0splitsn.c: |- ( ( ph /\ k e. A ) -> C e. ( 0 [,] +oo ) )
  assume sge0splitsn.d: |- ( k = B -> C = D )
  assume sge0splitsn.e: |- ( ph -> D e. ( 0 [,] +oo ) )

  disjoint A k
  disjoint B k
  disjoint D k
  disjoint k x
  assert |- ( ph -> ( sum^ ` ( k e. ( A u. { B } ) |-> C ) ) = ( ( sum^ ` ( k e. A |-> C ) ) +e D ) )

  proof
    wph
    vk
    cA
    cB
    csn
    #
    cun
    cC
    cmpt
    csumge0
    cfv
    vk
    cA
    cC
    cmpt
    csumge0
    cfv
    #
    vk
    @0
    cC
    cmpt
    csumge0
    cfv
    #
    cxad
    co
    @1
    cD
    cxad
    co
    wph
    vk
    cA
    @0
    cC
    cV
    cvv
    sge0splitsn.ph
    sge0splitsn.a
    wph
    @0
    cfn
    @0
    cfn
    wcel
    wph
    cB
    snfi
    a1i
    elexd
    wph
    cB
    cA
    wcel
    wn
    cA
    @0
    cin
    c0
    wceq
    sge0splitsn.n
    cA
    cB
    disjsn
    sylibr
    sge0splitsn.c
    wph
    vk
    cv
    #
    @0
    wcel
    #
    wa
    cC
    cD
    cc0
    cpnf
    cicc
    co
    #
    @4
    wph
    @3
    cB
    wceq
    #
    cC
    cD
    wceq
    #
    @3
    cB
    elsni
    @6
    @7
    wph
    sge0splitsn.d
    adantl
    sylan2
    wph
    cD
    @5
    wcel
    @4
    sge0splitsn.e
    adantr
    eqeltrd
    sge0splitmpt
    wph
    @2
    cD
    @1
    cxad
    wph
    cB
    cC
    cD
    vk
    cW
    sge0splitsn.ph
    sge0splitsn.b
    sge0splitsn.e
    sge0splitsn.d
    sge0snmptf
    oveq2d
    eqtrd
end
