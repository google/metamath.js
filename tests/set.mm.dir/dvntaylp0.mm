include "cc.mm"
include "cdvn.mm"
include "co.mm"
include "cfv.mm"
include "cmin.mm"
include "ctayl.mm"
include "caddc.mm"
include "cc0.mm"
include "cfz.mm"
include "wcel.mm"
include "cn0.mm"
include "elfz3nn0.mm"
include "syl.mm"
include "nn0cnd.mm"
include "elfznn0.mm"
include "npcand.mm"
include "oveq1d.mm"
include "syl6eqr.mm"
include "oveq2d.mm"
include "fveq1d.mm"
include "fznn0sub.mm"
include "cdm.mm"
include "fveq2d.mm"
include "dmeqd.mm"
include "eleqtrrd.mm"
include "dvntaylp.mm"
include "eqtr3d.mm"
include "wceq.mm"
include "cr.mm"
include "cpr.mm"
include "cpm.mm"
include "wf.mm"
include "cvv.mm"
include "wss.mm"
include "cnex.mm"
include "a1i.mm"
include "elpm2r.mm"
include "syl22anc.mm"
include "dvnf.mm"
include "syl3anc.mm"
include "dvnbss.mm"
include "fdm.mm"
include "sseqtrd.mm"
include "sstrd.mm"
include "cpnf.mm"
include "orcd.mm"
include "dvnadd.mm"
include "pncan3d.mm"
include "eqtrd.mm"
include "taylplem1.mm"
include "eqid.mm"
include "tayl0.mm"
include "simprd.mm"

theorem dvntaylp0
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cS: class S
  let cT: class T
  let cF: class F
  let cM: class M
  let cN: class N
  let vk: setvar k
  assume dvntaylp0.s: |- ( ph -> S e. { RR , CC } )
  assume dvntaylp0.f: |- ( ph -> F : A --> CC )
  assume dvntaylp0.a: |- ( ph -> A C_ S )
  assume dvntaylp0.m: |- ( ph -> M e. ( 0 ... N ) )
  assume dvntaylp0.b: |- ( ph -> B e. dom ( ( S Dn F ) ` N ) )
  assume dvntaylp0.t: |- T = ( N ( S Tayl F ) B )


  assert |- ( ph -> ( ( ( CC Dn T ) ` M ) ` B ) = ( ( ( S Dn F ) ` M ) ` B ) )

  proof
    wph
    cB
    cM
    cc
    cT
    cdvn
    co
    #
    cfv
    #
    cfv
    cB
    cN
    cM
    cmin
    co
    #
    cB
    cS
    cM
    cS
    cF
    cdvn
    co
    #
    cfv
    #
    ctayl
    co
    co
    #
    cfv
    #
    cB
    @4
    cfv
    #
    wph
    cB
    @1
    @5
    wph
    cM
    cc
    @2
    cM
    caddc
    co
    #
    cB
    cS
    cF
    ctayl
    co
    #
    co
    #
    cdvn
    co
    #
    cfv
    @1
    @5
    wph
    cM
    @11
    @0
    wph
    @10
    cT
    cc
    cdvn
    wph
    @10
    cN
    cB
    @9
    co
    cT
    wph
    @8
    cN
    cB
    @9
    wph
    cN
    cM
    wph
    cN
    wph
    cM
    cc0
    cN
    cfz
    co
    wcel
    #
    cN
    cn0
    wcel
    dvntaylp0.m
    cM
    cN
    elfz3nn0
    syl
    nn0cnd
    #
    wph
    cM
    wph
    @12
    cM
    cn0
    wcel
    #
    dvntaylp0.m
    cM
    cN
    elfznn0
    syl
    #
    nn0cnd
    #
    npcand
    #
    oveq1d
    dvntaylp0.t
    syl6eqr
    oveq2d
    fveq1d
    wph
    cA
    cB
    cS
    cF
    cM
    @2
    dvntaylp0.s
    dvntaylp0.f
    dvntaylp0.a
    @15
    wph
    @12
    @2
    cn0
    wcel
    #
    dvntaylp0.m
    cM
    cc0
    cN
    fznn0sub
    syl
    #
    wph
    cB
    cN
    @3
    cfv
    #
    cdm
    #
    @8
    @3
    cfv
    #
    cdm
    dvntaylp0.b
    wph
    @22
    @20
    wph
    @8
    cN
    @3
    @17
    fveq2d
    dmeqd
    eleqtrrd
    dvntaylp
    eqtr3d
    fveq1d
    wph
    cB
    @5
    cdm
    wcel
    @6
    @7
    wceq
    wph
    @4
    cdm
    #
    cB
    cS
    @5
    vk
    @4
    @2
    dvntaylp0.s
    wph
    cS
    cr
    cc
    cpr
    #
    wcel
    #
    cF
    cc
    cS
    cpm
    co
    wcel
    #
    @14
    @23
    cc
    @4
    wf
    dvntaylp0.s
    wph
    cc
    cvv
    wcel
    #
    @25
    cA
    cc
    cF
    wf
    #
    cA
    cS
    wss
    @26
    @27
    wph
    cnex
    a1i
    dvntaylp0.s
    dvntaylp0.f
    dvntaylp0.a
    cc
    cS
    cA
    cF
    cvv
    @24
    elpm2r
    syl22anc
    #
    @15
    cS
    cF
    cM
    dvnf
    syl3anc
    #
    wph
    @23
    cA
    cS
    wph
    @23
    cF
    cdm
    #
    cA
    wph
    @25
    @26
    @14
    @23
    @31
    wss
    dvntaylp0.s
    @29
    @15
    cS
    cF
    cM
    dvnbss
    syl3anc
    wph
    @28
    @31
    cA
    wceq
    dvntaylp0.f
    cA
    cc
    cF
    fdm
    syl
    sseqtrd
    dvntaylp0.a
    sstrd
    #
    wph
    @18
    @2
    cpnf
    wceq
    @19
    orcd
    wph
    @23
    cB
    cS
    vk
    @4
    @2
    dvntaylp0.s
    @30
    @32
    @19
    wph
    cB
    @21
    @2
    cS
    @4
    cdvn
    co
    cfv
    #
    cdm
    dvntaylp0.b
    wph
    @33
    @20
    wph
    @33
    cM
    @2
    caddc
    co
    #
    @3
    cfv
    #
    @20
    wph
    @25
    @26
    @14
    @18
    @33
    @35
    wceq
    dvntaylp0.s
    @29
    @15
    @19
    cS
    cF
    cM
    @2
    dvnadd
    syl22anc
    wph
    @34
    cN
    @3
    wph
    cM
    cN
    @16
    @13
    pncan3d
    fveq2d
    eqtrd
    dmeqd
    eleqtrrd
    taylplem1
    @5
    eqid
    tayl0
    simprd
    eqtrd
end
