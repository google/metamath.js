include "cmpt.mm"
include "csumge0.mm"
include "cfv.mm"
include "cv.mm"
include "cres.mm"
include "caddc.mm"
include "co.mm"
include "clt.mm"
include "wbr.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wrex.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "eqid.mm"
include "fmptdf.mm"
include "sge0ltfirp.mm"
include "wi.mm"
include "wcel.mm"
include "wa.mm"
include "simpr.mm"
include "wceq.mm"
include "elpwinss.mm"
include "resmptd.mm"
include "fveq2d.mm"
include "oveq1d.mm"
include "adantr.mm"
include "breqtrd.mm"
include "ex.mm"
include "reximia.mm"
include "a1i.mm"
include "mpd.mm"

theorem sge0ltfirpmpt
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cV: class V
  let cY: class Y
  let vk: setvar k
  assume sge0ltfirpmpt.xph: |- F/ x ph
  assume sge0ltfirpmpt.a: |- ( ph -> A e. V )
  assume sge0ltfirpmpt.b: |- ( ( ph /\ x e. A ) -> B e. ( 0 [,] +oo ) )
  assume sge0ltfirpmpt.rp: |- ( ph -> Y e. RR+ )
  assume sge0ltfirpmpt.re: |- ( ph -> ( sum^ ` ( x e. A |-> B ) ) e. RR )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B y
  disjoint Y y
  disjoint ph y
  disjoint k x
  assert |- ( ph -> E. y e. ( ~P A i^i Fin ) ( sum^ ` ( x e. A |-> B ) ) < ( ( sum^ ` ( x e. y |-> B ) ) + Y ) )

  proof
    wph
    vx
    cA
    cB
    cmpt
    #
    csumge0
    cfv
    #
    @0
    vy
    cv
    #
    cres
    #
    csumge0
    cfv
    #
    cY
    caddc
    co
    #
    clt
    wbr
    #
    vy
    cA
    cpw
    cfn
    cin
    #
    wrex
    #
    @1
    vx
    @2
    cB
    cmpt
    #
    csumge0
    cfv
    #
    cY
    caddc
    co
    #
    clt
    wbr
    #
    vy
    @7
    wrex
    #
    wph
    vy
    @0
    cV
    cA
    cY
    sge0ltfirpmpt.a
    wph
    vx
    cA
    cB
    cc0
    cpnf
    cicc
    co
    @0
    sge0ltfirpmpt.xph
    sge0ltfirpmpt.b
    @0
    eqid
    fmptdf
    sge0ltfirpmpt.rp
    sge0ltfirpmpt.re
    sge0ltfirp
    @8
    @13
    wi
    wph
    @6
    @12
    vy
    @7
    @2
    @7
    wcel
    #
    @6
    @12
    @14
    @6
    wa
    @1
    @5
    @11
    clt
    @14
    @6
    simpr
    @14
    @5
    @11
    wceq
    @6
    @14
    @4
    @10
    cY
    caddc
    @14
    @3
    @9
    csumge0
    @14
    vx
    cA
    @2
    cB
    @2
    cA
    cfn
    elpwinss
    resmptd
    fveq2d
    oveq1d
    adantr
    breqtrd
    ex
    reximia
    a1i
    mpd
end
