include "cv.mm"
include "c0.mm"
include "csupp.mm"
include "co.mm"
include "cep.mm"
include "coi.mm"
include "cdm.mm"
include "cvv.mm"
include "cfv.mm"
include "coe.mm"
include "comu.mm"
include "coa.mm"
include "cmpt2.mm"
include "cseqom.mm"
include "csb.mm"
include "ccnf.mm"
include "wcel.mm"
include "wa.mm"
include "fvex.mm"
include "csbex.mm"
include "a1i.mm"
include "cfsupp.mm"
include "wbr.mm"
include "cmap.mm"
include "crab.mm"
include "cmpt.mm"
include "eqid.mm"
include "cantnffval.mm"
include "cantnfdm.mm"
include "syl5eq.mm"
include "mpteq1d.mm"
include "eqtr4d.mm"
include "wceq.mm"
include "c1o.mm"
include "con0.mm"
include "adantr.mm"
include "simpr.mm"
include "cantnfval.mm"
include "cen.mm"
include "wwe.mm"
include "ovex.mm"
include "com.mm"
include "cantnfcl.mm"
include "simpld.mm"
include "oien.mm"
include "sylancr.mm"
include "wss.mm"
include "suppssdm.mm"
include "wf.mm"
include "cantnfs.mm"
include "simprbda.mm"
include "fdm.mm"
include "syl.mm"
include "syl5sseq.mm"
include "feq3.mm"
include "syl5ibcom.mm"
include "imp.mm"
include "f00.mm"
include "sylib.mm"
include "simprd.mm"
include "sseq0.mm"
include "syl2an2r.mm"
include "breqtrd.mm"
include "en0.mm"
include "fveq2d.mm"
include "0ex.mm"
include "seqom0g.mm"
include "mp1i.mm"
include "3eqtrd.mm"
include "el1o.mm"
include "sylibr.mm"
include "oveq2d.mm"
include "oe0.mm"
include "eqtrd.mm"
include "eleqtrrd.mm"
include "wne.mm"
include "wb.mm"
include "on0eln0.mm"
include "biimpar.mm"
include "cantnflt2.mm"
include "pm2.61dane.mm"
include "fmpt2d.mm"

theorem cantnff
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cS: class S
  let vc: setvar c
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let vk: setvar k
  let vn: setvar n
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let va: setvar a
  let vb: setvar b
  let vd: setvar d
  let cC: class C
  let cD: class D
  let cM: class M
  let cT: class T
  let cF: class F
  let cZ: class Z
  let cG: class G
  let cH: class H
  let cK: class K
  let cO: class O
  let cY: class Y
  let cX: class X
  assume cantnfs.s: |- S = dom ( A CNF B )
  assume cantnfs.a: |- ( ph -> A e. On )
  assume cantnfs.b: |- ( ph -> B e. On )


  assert |- ( ph -> ( A CNF B ) : S --> ( A ^o B ) )

  proof
    wph
    vf
    vx
    cS
    vh
    vf
    cv
    #
    c0
    csupp
    co
    cep
    coi
    #
    vh
    cv
    #
    cdm
    #
    vk
    vz
    cvv
    cvv
    cA
    vk
    cv
    #
    @2
    cfv
    #
    coe
    co
    @5
    @0
    cfv
    comu
    co
    vz
    cv
    #
    coa
    co
    cmpt2
    c0
    cseqom
    #
    cfv
    #
    csb
    #
    cA
    cB
    coe
    co
    #
    cA
    cB
    ccnf
    co
    #
    cvv
    @9
    cvv
    wcel
    wph
    @0
    cS
    wcel
    wa
    vh
    @1
    @8
    @3
    @7
    fvex
    csbex
    a1i
    wph
    @11
    vf
    vg
    cv
    c0
    cfsupp
    wbr
    vg
    cA
    cB
    cmap
    co
    crab
    #
    @9
    cmpt
    vf
    cS
    @9
    cmpt
    wph
    vz
    cA
    cB
    @12
    vf
    vg
    vh
    vk
    @12
    eqid
    #
    cantnfs.a
    cantnfs.b
    cantnffval
    wph
    vf
    cS
    @12
    @9
    wph
    cS
    @11
    cdm
    @12
    cantnfs.s
    wph
    cA
    cB
    @12
    vg
    @13
    cantnfs.a
    cantnfs.b
    cantnfdm
    syl5eq
    mpteq1d
    eqtr4d
    wph
    vx
    cv
    #
    cS
    wcel
    #
    wa
    #
    @14
    @11
    cfv
    #
    @10
    wcel
    cA
    c0
    @16
    cA
    c0
    wceq
    #
    wa
    #
    @17
    c1o
    @10
    @19
    @17
    c0
    wceq
    @17
    c1o
    wcel
    @19
    @17
    @14
    c0
    csupp
    co
    #
    cep
    coi
    #
    cdm
    #
    vk
    vz
    cvv
    cvv
    cA
    @4
    @21
    cfv
    #
    coe
    co
    @23
    @14
    cfv
    comu
    co
    @6
    coa
    co
    cmpt2
    #
    c0
    cseqom
    #
    cfv
    #
    c0
    @25
    cfv
    #
    c0
    @16
    @17
    @26
    wceq
    @18
    @16
    vz
    cA
    cB
    cS
    vk
    @14
    @21
    @25
    cantnfs.s
    wph
    cA
    con0
    wcel
    #
    @15
    cantnfs.a
    adantr
    #
    wph
    cB
    con0
    wcel
    #
    @15
    cantnfs.b
    adantr
    #
    @21
    eqid
    #
    wph
    @15
    simpr
    #
    @25
    eqid
    #
    cantnfval
    adantr
    @19
    @22
    c0
    @25
    @19
    @22
    c0
    cen
    wbr
    @22
    c0
    wceq
    @19
    @22
    @20
    c0
    cen
    @16
    @22
    @20
    cen
    wbr
    #
    @18
    @16
    @20
    cvv
    wcel
    @20
    cep
    wwe
    #
    @35
    @14
    c0
    csupp
    ovex
    @16
    @36
    @22
    com
    wcel
    @16
    cA
    cB
    cS
    @14
    @21
    cantnfs.s
    @29
    @31
    @32
    @33
    cantnfcl
    simpld
    @20
    cep
    @21
    cvv
    @32
    oien
    sylancr
    adantr
    @16
    @20
    cB
    wss
    #
    @18
    cB
    c0
    wceq
    #
    @20
    c0
    wceq
    @16
    @14
    cdm
    #
    @20
    cB
    @14
    c0
    suppssdm
    @16
    cB
    cA
    @14
    wf
    #
    @39
    cB
    wceq
    wph
    @15
    @40
    @14
    c0
    cfsupp
    wbr
    wph
    cA
    cB
    cS
    @14
    cantnfs.s
    cantnfs.a
    cantnfs.b
    cantnfs
    simprbda
    #
    cB
    cA
    @14
    fdm
    syl
    syl5sseq
    #
    @19
    @14
    c0
    wceq
    #
    @38
    @19
    cB
    c0
    @14
    wf
    #
    @43
    @38
    wa
    @16
    @18
    @44
    @16
    @40
    @18
    @44
    @41
    cA
    c0
    cB
    @14
    feq3
    syl5ibcom
    imp
    cB
    @14
    f00
    sylib
    simprd
    #
    @20
    cB
    sseq0
    syl2an2r
    breqtrd
    @22
    en0
    sylib
    fveq2d
    c0
    cvv
    wcel
    @27
    c0
    wceq
    @19
    0ex
    @24
    @25
    c0
    cvv
    @34
    seqom0g
    mp1i
    3eqtrd
    @17
    el1o
    sylibr
    @19
    @10
    cA
    c0
    coe
    co
    #
    c1o
    @19
    cB
    c0
    cA
    coe
    @45
    oveq2d
    @19
    @28
    @46
    c1o
    wceq
    @16
    @28
    @18
    @29
    adantr
    cA
    oe0
    syl
    eqtrd
    eleqtrrd
    @16
    cA
    c0
    wne
    #
    wa
    cA
    cB
    cB
    cS
    @14
    cantnfs.s
    @16
    @28
    @47
    @29
    adantr
    @16
    @30
    @47
    @31
    adantr
    #
    @16
    @15
    @47
    @33
    adantr
    @16
    c0
    cA
    wcel
    #
    @47
    @16
    @28
    @49
    @47
    wb
    @29
    cA
    on0eln0
    syl
    biimpar
    @48
    @16
    @37
    @47
    @42
    adantr
    cantnflt2
    pm2.61dane
    fmpt2d
end
