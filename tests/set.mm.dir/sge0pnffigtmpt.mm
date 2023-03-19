include "cmpt.mm"
include "cv.mm"
include "cres.mm"
include "csumge0.mm"
include "cfv.mm"
include "clt.mm"
include "wbr.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wrex.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "eqid.mm"
include "fmptdf.mm"
include "sge0pnffigt.mm"
include "wcel.mm"
include "wi.mm"
include "wa.mm"
include "simpr.mm"
include "wss.mm"
include "elpwinss.mm"
include "adantr.mm"
include "resmptd.mm"
include "fveq2d.mm"
include "breqtrd.mm"
include "ex.mm"
include "adantl.mm"
include "reximdva.mm"
include "mpd.mm"

theorem sge0pnffigtmpt
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cV: class V
  let cY: class Y
  assume sge0pnffigtmpt.k: |- F/ k ph
  assume sge0pnffigtmpt.a: |- ( ph -> A e. V )
  assume sge0pnffigtmpt.b: |- ( ( ph /\ k e. A ) -> B e. ( 0 [,] +oo ) )
  assume sge0pnffigtmpt.p: |- ( ph -> ( sum^ ` ( k e. A |-> B ) ) = +oo )
  assume sge0pnffigtmpt.y: |- ( ph -> Y e. RR )

  disjoint A k
  disjoint A x
  disjoint k x
  disjoint B x
  disjoint Y x
  disjoint ph x
  disjoint k x
  assert |- ( ph -> E. x e. ( ~P A i^i Fin ) Y < ( sum^ ` ( k e. x |-> B ) ) )

  proof
    wph
    cY
    vk
    cA
    cB
    cmpt
    #
    vx
    cv
    #
    cres
    #
    csumge0
    cfv
    #
    clt
    wbr
    #
    vx
    cA
    cpw
    cfn
    cin
    #
    wrex
    cY
    vk
    @1
    cB
    cmpt
    #
    csumge0
    cfv
    #
    clt
    wbr
    #
    vx
    @5
    wrex
    wph
    vx
    @0
    cV
    cA
    cY
    sge0pnffigtmpt.a
    wph
    vk
    cA
    cB
    cc0
    cpnf
    cicc
    co
    @0
    sge0pnffigtmpt.k
    sge0pnffigtmpt.b
    @0
    eqid
    fmptdf
    sge0pnffigtmpt.p
    sge0pnffigtmpt.y
    sge0pnffigt
    wph
    @4
    @8
    vx
    @5
    @1
    @5
    wcel
    #
    @4
    @8
    wi
    wph
    @9
    @4
    @8
    @9
    @4
    wa
    #
    cY
    @3
    @7
    clt
    @9
    @4
    simpr
    @10
    @2
    @6
    csumge0
    @10
    vk
    cA
    @1
    cB
    @9
    @1
    cA
    wss
    @4
    @1
    cA
    cfn
    elpwinss
    adantr
    resmptd
    fveq2d
    breqtrd
    ex
    adantl
    reximdva
    mpd
end
