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
include "csu.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "eqid.mm"
include "fmptdf.mm"
include "sge0ltfirp.mm"
include "wcel.mm"
include "wa.mm"
include "simpr.mm"
include "wceq.mm"
include "elpwinss.mm"
include "resmptd.mm"
include "fveq2d.mm"
include "adantl.mm"
include "elinel2.mm"
include "cico.mm"
include "nfv.mm"
include "nfan.mm"
include "simpll.mm"
include "sselda.mm"
include "adantll.mm"
include "sge0rernmpt.mm"
include "syl2anc.mm"
include "sge0fsum.mm"
include "csb.mm"
include "wi.mm"
include "nfcsb1v.mm"
include "nfel1.mm"
include "nfim.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "csbeq1a.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "chvar.mm"
include "nfcv.mm"
include "cbvmpt.mm"
include "fvmpt2.mm"
include "sumeq2dv.mm"
include "eqcom.mm"
include "imbi1i.mm"
include "imbi2i.mm"
include "bitri.mm"
include "mpbi.mm"
include "cbvsum.mm"
include "a1i.mm"
include "eqtrd.mm"
include "3eqtrd.mm"
include "oveq1d.mm"
include "adantr.mm"
include "breqtrd.mm"
include "ex.mm"
include "reximdva.mm"
include "mpd.mm"

theorem sge0ltfirpmpt2
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cA: class A
  let cB: class B
  let cV: class V
  let cY: class Y
  let vk: setvar k
  assume sge0ltfirpmpt2.xph: |- F/ x ph
  assume sge0ltfirpmpt2.a: |- ( ph -> A e. V )
  assume sge0ltfirpmpt2.b: |- ( ( ph /\ x e. A ) -> B e. ( 0 [,] +oo ) )
  assume sge0ltfirpmpt2.rp: |- ( ph -> Y e. RR+ )
  assume sge0ltfirpmpt2.re: |- ( ph -> ( sum^ ` ( x e. A |-> B ) ) e. RR )

  disjoint A x
  disjoint A y
  disjoint x y
  disjoint B y
  disjoint Y y
  disjoint ph y
  disjoint A k
  disjoint k x
  disjoint k y
  disjoint B k
  disjoint k ph
  disjoint k x
  assert |- ( ph -> E. y e. ( ~P A i^i Fin ) ( sum^ ` ( x e. A |-> B ) ) < ( sum_ x e. y B + Y ) )

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
    #
    cfn
    cin
    #
    wrex
    @1
    @2
    cB
    vx
    csu
    #
    cY
    caddc
    co
    #
    clt
    wbr
    #
    vy
    @8
    wrex
    wph
    vy
    @0
    cV
    cA
    cY
    sge0ltfirpmpt2.a
    wph
    vx
    cA
    cB
    cc0
    cpnf
    cicc
    co
    @0
    sge0ltfirpmpt2.xph
    sge0ltfirpmpt2.b
    @0
    eqid
    fmptdf
    sge0ltfirpmpt2.rp
    sge0ltfirpmpt2.re
    sge0ltfirp
    wph
    @6
    @11
    vy
    @8
    wph
    @2
    @8
    wcel
    #
    wa
    #
    @6
    @11
    @13
    @6
    wa
    @1
    @5
    @10
    clt
    @13
    @6
    simpr
    @13
    @5
    @10
    wceq
    @6
    @13
    @4
    @9
    cY
    caddc
    @13
    @4
    vx
    @2
    cB
    cmpt
    #
    csumge0
    cfv
    #
    @2
    vk
    cv
    #
    @14
    cfv
    #
    vk
    csu
    #
    @9
    @12
    @4
    @15
    wceq
    wph
    @12
    @3
    @14
    csumge0
    @12
    vx
    cA
    @2
    cB
    @2
    cA
    cfn
    elpwinss
    #
    resmptd
    fveq2d
    adantl
    @13
    vk
    @14
    @2
    @12
    @2
    cfn
    wcel
    wph
    @2
    @7
    cfn
    elinel2
    adantl
    @13
    vx
    @2
    cB
    cc0
    cpnf
    cico
    co
    #
    @14
    wph
    @12
    vx
    sge0ltfirpmpt2.xph
    @12
    vx
    nfv
    nfan
    @13
    vx
    cv
    #
    @2
    wcel
    #
    wa
    wph
    @21
    cA
    wcel
    #
    cB
    @20
    wcel
    #
    wph
    @12
    @22
    simpll
    @12
    @22
    @23
    wph
    @12
    @2
    cA
    @21
    @19
    sselda
    adantll
    wph
    vx
    cA
    cB
    cV
    sge0ltfirpmpt2.xph
    sge0ltfirpmpt2.a
    sge0ltfirpmpt2.b
    sge0ltfirpmpt2.re
    sge0rernmpt
    #
    syl2anc
    @14
    eqid
    fmptdf
    sge0fsum
    @13
    @18
    @2
    vx
    @16
    cB
    csb
    #
    vk
    csu
    #
    @9
    @13
    @2
    @17
    @26
    vk
    @13
    @16
    @2
    wcel
    #
    wa
    #
    @28
    @26
    @20
    wcel
    #
    @17
    @26
    wceq
    @13
    @28
    simpr
    @29
    wph
    @16
    cA
    wcel
    #
    @30
    wph
    @12
    @28
    simpll
    @12
    @28
    @31
    wph
    @12
    @2
    cA
    @16
    @19
    sselda
    adantll
    wph
    @23
    wa
    #
    @24
    wi
    wph
    @31
    wa
    #
    @30
    wi
    vx
    vk
    @33
    @30
    vx
    wph
    @31
    vx
    sge0ltfirpmpt2.xph
    @31
    vx
    nfv
    nfan
    vx
    @26
    @20
    vx
    @16
    cB
    nfcsb1v
    #
    nfel1
    nfim
    @21
    @16
    wceq
    #
    @32
    @33
    @24
    @30
    @35
    @23
    @31
    wph
    @21
    @16
    cA
    eleq1
    anbi2d
    @35
    cB
    @26
    @20
    vx
    @16
    cB
    csbeq1a
    #
    eleq1d
    imbi12d
    @25
    chvar
    syl2anc
    vk
    @2
    @26
    @20
    @14
    vx
    vk
    @2
    cB
    @26
    vk
    cB
    nfcv
    #
    @34
    @36
    cbvmpt
    fvmpt2
    syl2anc
    sumeq2dv
    @27
    @9
    wceq
    @13
    @2
    @26
    cB
    vk
    vx
    @35
    cB
    @26
    wceq
    #
    wi
    #
    @16
    @21
    wceq
    #
    @26
    cB
    wceq
    #
    wi
    #
    @36
    @39
    @40
    @38
    wi
    @42
    @35
    @40
    @38
    @21
    @16
    eqcom
    imbi1i
    @38
    @41
    @40
    cB
    @26
    eqcom
    imbi2i
    bitri
    mpbi
    vx
    @2
    nfcv
    vk
    @2
    nfcv
    @34
    @37
    cbvsum
    a1i
    eqtrd
    3eqtrd
    oveq1d
    adantr
    breqtrd
    ex
    reximdva
    mpd
end
