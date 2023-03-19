include "c0.mm"
include "wceq.mm"
include "covoln.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cc0.mm"
include "0le0.mm"
include "a1i.mm"
include "fveq2.mm"
include "fveq1d.mm"
include "adantl.mm"
include "cr.mm"
include "cmap.mm"
include "co.mm"
include "wss.mm"
include "adantr.mm"
include "simpr.mm"
include "oveq2d.mm"
include "sseqtrd.mm"
include "sstrd.mm"
include "ovn0val.mm"
include "eqtrd.mm"
include "breq12d.mm"
include "mpbird.mm"
include "wn.mm"
include "cn.mm"
include "cv.mm"
include "cico.mm"
include "ccom.mm"
include "cixp.mm"
include "ciun.mm"
include "cvol.mm"
include "cprod.mm"
include "cmpt.mm"
include "csumge0.mm"
include "cxp.mm"
include "wrex.mm"
include "cxr.mm"
include "crab.mm"
include "cfn.mm"
include "wcel.mm"
include "wne.mm"
include "neqne.mm"
include "eqid.mm"
include "ovnsslelem.mm"
include "pm2.61dan.mm"

theorem ovnssle
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cX: class X
  let vi: setvar i
  let vz: setvar z
  let vj: setvar j
  let vk: setvar k
  let vx: setvar x
  assume ovnssle.1: |- ( ph -> X e. Fin )
  assume ovnssle.2: |- ( ph -> A C_ B )
  assume ovnssle.3: |- ( ph -> B C_ ( RR ^m X ) )


  assert |- ( ph -> ( ( voln* ` X ) ` A ) <_ ( ( voln* ` X ) ` B ) )

  proof
    wph
    cX
    c0
    wceq
    #
    cA
    cX
    covoln
    cfv
    #
    cfv
    #
    cB
    @1
    cfv
    #
    cle
    wbr
    #
    wph
    @0
    wa
    #
    @4
    cc0
    cc0
    cle
    wbr
    #
    @6
    @5
    0le0
    a1i
    @5
    @2
    cc0
    @3
    cc0
    cle
    @5
    @2
    cA
    c0
    covoln
    cfv
    #
    cfv
    #
    cc0
    @0
    @2
    @8
    wceq
    wph
    @0
    cA
    @1
    @7
    cX
    c0
    covoln
    fveq2
    #
    fveq1d
    adantl
    @5
    cA
    @5
    cA
    cB
    cr
    c0
    cmap
    co
    #
    wph
    cA
    cB
    wss
    #
    @0
    ovnssle.2
    adantr
    @5
    cB
    cr
    cX
    cmap
    co
    #
    @10
    wph
    cB
    @12
    wss
    #
    @0
    ovnssle.3
    adantr
    @5
    cX
    c0
    cr
    cmap
    wph
    @0
    simpr
    oveq2d
    sseqtrd
    #
    sstrd
    ovn0val
    eqtrd
    @5
    @3
    cB
    @7
    cfv
    #
    cc0
    @0
    @3
    @15
    wceq
    wph
    @0
    cB
    @1
    @7
    @9
    fveq1d
    adantl
    @5
    cB
    @14
    ovn0val
    eqtrd
    breq12d
    mpbird
    wph
    @0
    wn
    #
    wa
    vz
    cA
    cB
    vi
    vj
    vk
    cA
    vj
    cn
    vk
    cX
    vk
    cv
    cico
    vj
    cv
    vi
    cv
    cfv
    ccom
    cfv
    #
    cixp
    ciun
    #
    wss
    vz
    cv
    vj
    cn
    cX
    @17
    cvol
    cfv
    vk
    cprod
    cmpt
    csumge0
    cfv
    wceq
    #
    wa
    vi
    cr
    cr
    cxp
    cX
    cmap
    co
    cn
    cmap
    co
    #
    wrex
    vz
    cxr
    crab
    #
    cB
    @18
    wss
    @19
    wa
    vi
    @20
    wrex
    vz
    cxr
    crab
    #
    cX
    wph
    cX
    cfn
    wcel
    @16
    ovnssle.1
    adantr
    @16
    cX
    c0
    wne
    wph
    cX
    c0
    neqne
    adantl
    wph
    @11
    @16
    ovnssle.2
    adantr
    wph
    @13
    @16
    ovnssle.3
    adantr
    @21
    eqid
    @22
    eqid
    ovnsslelem
    pm2.61dan
end
