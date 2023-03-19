include "cv.mm"
include "csn.mm"
include "cxp.mm"
include "ciun.mm"
include "cmpt.mm"
include "csumge0.mm"
include "cfv.mm"
include "cvv.mm"
include "wcel.mm"
include "snex.mm"
include "a1i.mm"
include "xpexg.mm"
include "syl2anc.mm"
include "adantr.mm"
include "wdisj.mm"
include "disjsnxp.mm"
include "cc0.mm"
include "cpnf.mm"
include "cicc.mm"
include "co.mm"
include "wa.mm"
include "cop.mm"
include "wceq.mm"
include "wrex.mm"
include "wb.mm"
include "vex.mm"
include "elsnxp.mm"
include "ax-mp.mm"
include "biimpi.mm"
include "adantl.mm"
include "nfv.mm"
include "nfan.mm"
include "wi.mm"
include "w3a.mm"
include "3ad2ant3.mm"
include "3expa.mm"
include "3adant3.mm"
include "eqeltrd.mm"
include "3exp.mm"
include "rexlimd.mm"
include "mpd.mm"
include "3impa.mm"
include "sge0iunmpt.mm"
include "iunxpconst.mm"
include "eqcomi.mm"
include "mpteq1d.mm"
include "fveq2d.mm"
include "simpr.mm"
include "eqid.mm"
include "projf1o.mm"
include "eqidd.mm"
include "opeq2.mm"
include "opex.mm"
include "fvmptd.mm"
include "adantlr.mm"
include "sge0f1o.mm"
include "eqcomd.mm"
include "mpteq2da.mm"
include "3eqtr4rd.mm"

theorem sge0xp
  let wph: wff ph
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let vj: setvar j
  let vk: setvar k
  let cV: class V
  let cW: class W
  let vi: setvar i
  let vx: setvar x
  assume sge0xp.1: |- F/ k ph
  assume sge0xp.z: |- ( z = <. j , k >. -> D = C )
  assume sge0xp.a: |- ( ph -> A e. V )
  assume sge0xp.b: |- ( ph -> B e. W )
  assume sge0xp.d: |- ( ( ph /\ j e. A /\ k e. B ) -> C e. ( 0 [,] +oo ) )

  disjoint A j
  disjoint A k
  disjoint A z
  disjoint j k
  disjoint j z
  disjoint k z
  disjoint B j
  disjoint B k
  disjoint B z
  disjoint C z
  disjoint D j
  disjoint D k
  disjoint j ph
  disjoint ph z
  disjoint B i
  disjoint i j
  disjoint i k
  disjoint i z
  disjoint i ph
  disjoint k x
  assert |- ( ph -> ( sum^ ` ( j e. A |-> ( sum^ ` ( k e. B |-> C ) ) ) ) = ( sum^ ` ( z e. ( A X. B ) |-> D ) ) )

  proof
    wph
    vz
    vj
    cA
    vj
    cv
    #
    csn
    #
    cB
    cxp
    #
    ciun
    #
    cD
    cmpt
    #
    csumge0
    cfv
    vj
    cA
    vz
    @2
    cD
    cmpt
    csumge0
    cfv
    #
    cmpt
    #
    csumge0
    cfv
    vz
    cA
    cB
    cxp
    #
    cD
    cmpt
    #
    csumge0
    cfv
    vj
    cA
    vk
    cB
    cC
    cmpt
    csumge0
    cfv
    #
    cmpt
    #
    csumge0
    cfv
    wph
    vj
    cA
    @2
    cD
    vz
    cV
    cvv
    sge0xp.a
    wph
    @2
    cvv
    wcel
    #
    @0
    cA
    wcel
    #
    wph
    @1
    cvv
    wcel
    #
    cB
    cW
    wcel
    #
    @11
    @13
    wph
    @0
    snex
    a1i
    sge0xp.b
    @1
    cB
    cvv
    cW
    xpexg
    syl2anc
    adantr
    vj
    cA
    @2
    wdisj
    wph
    cA
    cB
    vj
    disjsnxp
    a1i
    wph
    @12
    vz
    cv
    #
    @2
    wcel
    #
    cD
    cc0
    cpnf
    cicc
    co
    #
    wcel
    #
    wph
    @12
    wa
    #
    @16
    wa
    #
    @15
    @0
    vk
    cv
    #
    cop
    #
    wceq
    #
    vk
    cB
    wrex
    #
    @18
    @16
    @24
    @19
    @16
    @24
    @0
    cvv
    wcel
    @16
    @24
    wb
    vj
    vex
    vk
    cB
    cvv
    @0
    @15
    elsnxp
    ax-mp
    biimpi
    adantl
    @20
    @23
    @18
    vk
    cB
    @19
    @16
    vk
    wph
    @12
    vk
    sge0xp.1
    @12
    vk
    nfv
    nfan
    #
    @16
    vk
    nfv
    nfan
    @18
    vk
    nfv
    @19
    @21
    cB
    wcel
    #
    @23
    @18
    wi
    wi
    @16
    @19
    @26
    @23
    @18
    @19
    @26
    @23
    w3a
    cD
    cC
    @17
    @23
    @19
    cD
    cC
    wceq
    @26
    sge0xp.z
    3ad2ant3
    @19
    @26
    cC
    @17
    wcel
    #
    @23
    wph
    @12
    @26
    @27
    sge0xp.d
    3expa
    3adant3
    eqeltrd
    3exp
    adantr
    rexlimd
    mpd
    #
    3impa
    sge0iunmpt
    wph
    @8
    @4
    csumge0
    wph
    vz
    @7
    @3
    cD
    @7
    @3
    wceq
    wph
    @3
    @7
    vj
    cA
    cB
    iunxpconst
    eqcomi
    a1i
    mpteq1d
    fveq2d
    wph
    @10
    @6
    csumge0
    wph
    vj
    cA
    @9
    @5
    wph
    vj
    nfv
    @19
    @5
    @9
    @19
    @2
    cD
    cB
    cC
    vz
    vk
    vi
    cB
    @0
    vi
    cv
    #
    cop
    #
    cmpt
    #
    @22
    cW
    @19
    vz
    nfv
    @25
    sge0xp.z
    wph
    @14
    @12
    sge0xp.b
    adantr
    @19
    vi
    @0
    cB
    @31
    cA
    wph
    @12
    simpr
    @31
    eqid
    projf1o
    wph
    @26
    @21
    @31
    cfv
    @22
    wceq
    @12
    wph
    @26
    wa
    #
    vi
    @21
    @30
    @22
    cB
    @31
    cvv
    @32
    @31
    eqidd
    @29
    @21
    wceq
    @30
    @22
    wceq
    @32
    @29
    @21
    @0
    opeq2
    adantl
    wph
    @26
    simpr
    @22
    cvv
    wcel
    @32
    @0
    @21
    opex
    a1i
    fvmptd
    adantlr
    @28
    sge0f1o
    eqcomd
    mpteq2da
    fveq2d
    3eqtr4rd
end
