include "cv.mm"
include "csb.mm"
include "csu.mm"
include "cmpt.mm"
include "csumge0.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "wceq.mm"
include "simpr.mm"
include "wi.mm"
include "nfv.mm"
include "nfan.mm"
include "nfcv.mm"
include "nfcsb1.mm"
include "nfel1.mm"
include "nfim.mm"
include "eleq1.mm"
include "anbi2d.mm"
include "csbeq1a.mm"
include "eleq1d.mm"
include "imbi12d.mm"
include "chvar.mm"
include "nfcsb1v.mm"
include "cbvmpt.mm"
include "eqcomi.mm"
include "fvmptf.mm"
include "syl2anc.mm"
include "cc.mm"
include "cr.mm"
include "rge0ssre.mm"
include "ax-resscn.mm"
include "sstri.mm"
include "sseldi.mm"
include "caddc.mm"
include "cseq.mm"
include "cli.mm"
include "wbr.mm"
include "a1i.mm"
include "seqeq3d.mm"
include "breq1d.mm"
include "mpbid.mm"
include "isumclim.mm"
include "cbvsum.mm"
include "sge0isummpt.mm"
include "3eqtr4rd.mm"

theorem sge0isummpt2
  let wph: wff ph
  let cA: class A
  let cB: class B
  let vk: setvar k
  let cM: class M
  let cZ: class Z
  let vi: setvar i
  let vj: setvar j
  let vx: setvar x
  assume sge0isummpt2.kph: |- F/ k ph
  assume sge0isummpt2.a: |- ( ( ph /\ k e. Z ) -> A e. ( 0 [,) +oo ) )
  assume sge0isummpt2.m: |- ( ph -> M e. ZZ )
  assume sge0isummpt2.z: |- Z = ( ZZ>= ` M )
  assume sge0isummpt2.b: |- ( ph -> seq M ( + , ( k e. Z |-> A ) ) ~~> B )

  disjoint Z k
  disjoint A i
  disjoint A j
  disjoint i j
  disjoint M j
  disjoint Z i
  disjoint Z j
  disjoint i k
  disjoint j k
  disjoint j ph
  disjoint k x
  assert |- ( ph -> ( sum^ ` ( k e. Z |-> A ) ) = sum_ k e. Z A )

  proof
    wph
    cZ
    vk
    vj
    cv
    #
    cA
    csb
    #
    vj
    csu
    #
    cB
    cZ
    cA
    vk
    csu
    #
    vk
    cZ
    cA
    cmpt
    #
    csumge0
    cfv
    wph
    @1
    cB
    vj
    vi
    cZ
    vk
    vi
    cv
    #
    cA
    csb
    #
    cmpt
    #
    cM
    cZ
    sge0isummpt2.z
    sge0isummpt2.m
    wph
    @0
    cZ
    wcel
    #
    wa
    #
    @8
    @1
    cc0
    cpnf
    cico
    co
    #
    wcel
    #
    @0
    @7
    cfv
    @1
    wceq
    wph
    @8
    simpr
    wph
    vk
    cv
    #
    cZ
    wcel
    #
    wa
    #
    cA
    @10
    wcel
    #
    wi
    @9
    @11
    wi
    vk
    vj
    @9
    @11
    vk
    wph
    @8
    vk
    sge0isummpt2.kph
    @8
    vk
    nfv
    nfan
    vk
    @1
    @10
    vk
    @0
    cA
    vk
    @0
    nfcv
    #
    nfcsb1
    #
    nfel1
    nfim
    @12
    @0
    wceq
    #
    @14
    @9
    @15
    @11
    @18
    @13
    @8
    wph
    @12
    @0
    cZ
    eleq1
    anbi2d
    @18
    cA
    @1
    @10
    vk
    @0
    cA
    csbeq1a
    #
    eleq1d
    imbi12d
    sge0isummpt2.a
    chvar
    #
    vk
    @0
    cA
    @1
    cZ
    @7
    @10
    @16
    @17
    @19
    @4
    @7
    vk
    vi
    cZ
    cA
    @6
    vi
    cA
    nfcv
    vk
    @5
    cA
    nfcsb1v
    vk
    @5
    cA
    csbeq1a
    cbvmpt
    #
    eqcomi
    fvmptf
    syl2anc
    @9
    @10
    cc
    @1
    @10
    cr
    cc
    rge0ssre
    ax-resscn
    sstri
    @20
    sseldi
    wph
    caddc
    @4
    cM
    cseq
    #
    cB
    cli
    wbr
    caddc
    @7
    cM
    cseq
    #
    cB
    cli
    wbr
    sge0isummpt2.b
    wph
    @22
    @23
    cB
    cli
    wph
    @4
    @7
    caddc
    cM
    @4
    @7
    wceq
    wph
    @21
    a1i
    seqeq3d
    breq1d
    mpbid
    isumclim
    @3
    @2
    wceq
    wph
    cZ
    cA
    @1
    vk
    vj
    @19
    vj
    cZ
    nfcv
    vk
    cZ
    nfcv
    vj
    cA
    nfcv
    @17
    cbvsum
    a1i
    wph
    cA
    cB
    vk
    cM
    cZ
    sge0isummpt2.kph
    sge0isummpt2.a
    sge0isummpt2.m
    sge0isummpt2.z
    sge0isummpt2.b
    sge0isummpt
    3eqtr4rd
end
