include "climc.mm"
include "co.mm"
include "csn.mm"
include "cdif.mm"
include "cres.mm"
include "cc.mm"
include "wss.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "cdm.mm"
include "wceq.mm"
include "wf.mm"
include "fdm.mm"
include "syl.mm"
include "adantr.mm"
include "w3a.mm"
include "limcrcl.mm"
include "adantl.mm"
include "simp2d.mm"
include "eqsstr3d.mm"
include "simp3d.mm"
include "jca.mm"
include "ex.mm"
include "cun.mm"
include "undif1.mm"
include "difss.mm"
include "fssres.mm"
include "sylancl.mm"
include "snssd.mm"
include "unssd.mm"
include "syl5eqssr.mm"
include "unssad.mm"
include "wb.mm"
include "cfv.mm"
include "cif.mm"
include "cmpt.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "crest.mm"
include "ccnp.mm"
include "eqid.mm"
include "simprl.mm"
include "simprr.mm"
include "ellimc.mm"
include "eqcomi.mm"
include "oveq2i.mm"
include "mpteq12i.mm"
include "wo.mm"
include "elun.mm"
include "velsn.mm"
include "orbi2i.mm"
include "wn.mm"
include "pm5.61.mm"
include "fvres.mm"
include "sylbi.mm"
include "ifeq2da.mm"
include "mpteq2ia.mm"
include "eqtr4i.mm"
include "ssdifssd.mm"
include "bitr4d.mm"
include "pm5.21ndd.mm"
include "eqrdv.mm"

theorem limcdif
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cF: class F
  let vf: setvar f
  let vj: setvar j
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let cC: class C
  let cK: class K
  assume limccl.f: |- ( ph -> F : A --> CC )


  assert |- ( ph -> ( F limCC B ) = ( ( F |` ( A \ { B } ) ) limCC B ) )

  proof
    wph
    vx
    cF
    cB
    climc
    co
    #
    cF
    cA
    cB
    csn
    #
    cdif
    #
    cres
    #
    cB
    climc
    co
    #
    wph
    cA
    cc
    wss
    #
    cB
    cc
    wcel
    #
    wa
    #
    vx
    cv
    #
    @0
    wcel
    #
    @8
    @4
    wcel
    #
    wph
    @9
    @7
    wph
    @9
    wa
    #
    @5
    @6
    @11
    cA
    cF
    cdm
    #
    cc
    wph
    @12
    cA
    wceq
    #
    @9
    wph
    cA
    cc
    cF
    wf
    #
    @13
    limccl.f
    cA
    cc
    cF
    fdm
    syl
    adantr
    @11
    @12
    cc
    cF
    wf
    #
    @12
    cc
    wss
    #
    @6
    @9
    @15
    @16
    @6
    w3a
    wph
    cB
    @8
    cF
    limcrcl
    adantl
    #
    simp2d
    eqsstr3d
    @11
    @15
    @16
    @6
    @17
    simp3d
    jca
    ex
    wph
    @10
    @7
    wph
    @10
    wa
    #
    @5
    @6
    @18
    cA
    @1
    cc
    @18
    cA
    @1
    cun
    #
    @2
    @1
    cun
    #
    cc
    cA
    @1
    undif1
    #
    @18
    @2
    @1
    cc
    @18
    @2
    @3
    cdm
    #
    cc
    wph
    @22
    @2
    wceq
    #
    @10
    wph
    @2
    cc
    @3
    wf
    #
    @23
    wph
    @14
    @2
    cA
    wss
    @24
    limccl.f
    cA
    @1
    difss
    cA
    cc
    @2
    cF
    fssres
    sylancl
    #
    @2
    cc
    @3
    fdm
    syl
    adantr
    @18
    @22
    cc
    @3
    wf
    #
    @22
    cc
    wss
    #
    @6
    @10
    @26
    @27
    @6
    w3a
    wph
    cB
    @8
    @3
    limcrcl
    adantl
    #
    simp2d
    eqsstr3d
    @18
    cB
    cc
    @18
    @26
    @27
    @6
    @28
    simp3d
    #
    snssd
    unssd
    syl5eqssr
    unssad
    @29
    jca
    ex
    wph
    @7
    @9
    @10
    wb
    wph
    @7
    wa
    #
    @9
    vz
    @19
    vz
    cv
    #
    cB
    wceq
    #
    @8
    @31
    cF
    cfv
    #
    cif
    #
    cmpt
    #
    cB
    ccnfld
    ctopn
    cfv
    #
    @19
    crest
    co
    #
    @36
    ccnp
    co
    cfv
    wcel
    @10
    @30
    vz
    cA
    cB
    @8
    cF
    @35
    @37
    @36
    @37
    eqid
    @36
    eqid
    #
    @35
    eqid
    wph
    @14
    @7
    limccl.f
    adantr
    wph
    @5
    @6
    simprl
    #
    wph
    @5
    @6
    simprr
    #
    ellimc
    @30
    vz
    @2
    cB
    @8
    @3
    @35
    @37
    @36
    @19
    @20
    @36
    crest
    @20
    @19
    @21
    eqcomi
    #
    oveq2i
    @38
    @35
    vz
    @20
    @34
    cmpt
    vz
    @20
    @32
    @8
    @31
    @3
    cfv
    #
    cif
    #
    cmpt
    vz
    @19
    @34
    @20
    @34
    @41
    @34
    eqid
    mpteq12i
    vz
    @20
    @43
    @34
    @31
    @20
    wcel
    @31
    @2
    wcel
    #
    @31
    @1
    wcel
    #
    wo
    #
    @43
    @34
    wceq
    #
    @31
    @2
    @1
    elun
    @46
    @44
    @32
    wo
    #
    @47
    @45
    @32
    @44
    vz
    cB
    velsn
    orbi2i
    @48
    @32
    @42
    @33
    @8
    @48
    @32
    wn
    #
    wa
    @44
    @49
    wa
    @42
    @33
    wceq
    #
    @44
    @32
    pm5.61
    @44
    @50
    @49
    @31
    @2
    cF
    fvres
    adantr
    sylbi
    ifeq2da
    sylbi
    sylbi
    mpteq2ia
    eqtr4i
    wph
    @24
    @7
    @25
    adantr
    @30
    cA
    cc
    @1
    @39
    ssdifssd
    @40
    ellimc
    bitr4d
    ex
    pm5.21ndd
    eqrdv
end
