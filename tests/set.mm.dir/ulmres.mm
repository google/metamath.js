include "cvv.mm"
include "wcel.mm"
include "cc.mm"
include "wf.mm"
include "wa.mm"
include "culm.mm"
include "cfv.mm"
include "wbr.mm"
include "cres.mm"
include "wi.mm"
include "ulmscl.mm"
include "ulmcl.mm"
include "jca.mm"
include "a1i.mm"
include "wb.mm"
include "cv.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "clt.mm"
include "wral.mm"
include "cuz.mm"
include "wrex.mm"
include "crp.mm"
include "cz.mm"
include "syl6eleq.mm"
include "adantr.mm"
include "eluzel2.mm"
include "syl.mm"
include "rexuz3.mm"
include "eluzelz.mm"
include "bitr4d.mm"
include "ralbidv.mm"
include "cmap.mm"
include "eqidd.mm"
include "simprr.mm"
include "simprl.mm"
include "ulm2.mm"
include "wss.mm"
include "uzss.mm"
include "3sstr4g.mm"
include "fssresd.mm"
include "wceq.mm"
include "fvres.mm"
include "ad2antrl.mm"
include "fveq1d.mm"
include "3bitr4d.mm"
include "ex.mm"
include "pm5.21ndd.mm"

theorem ulmres
  let wph: wff ph
  let cS: class S
  let cF: class F
  let cG: class G
  let cM: class M
  let cN: class N
  let cW: class W
  let cZ: class Z
  let vj: setvar j
  let vk: setvar k
  let vr: setvar r
  let vz: setvar z
  assume ulmres.z: |- Z = ( ZZ>= ` M )
  assume ulmres.w: |- W = ( ZZ>= ` N )
  assume ulmres.m: |- ( ph -> N e. Z )
  assume ulmres.f: |- ( ph -> F : Z --> ( CC ^m S ) )


  assert |- ( ph -> ( F ( ~~>u ` S ) G <-> ( F |` W ) ( ~~>u ` S ) G ) )

  proof
    wph
    cS
    cvv
    wcel
    #
    cS
    cc
    cG
    wf
    #
    wa
    #
    cF
    cG
    cS
    culm
    cfv
    #
    wbr
    #
    cF
    cW
    cres
    #
    cG
    @3
    wbr
    #
    @4
    @2
    wi
    wph
    @4
    @0
    @1
    cS
    cF
    cG
    ulmscl
    cS
    cF
    cG
    ulmcl
    jca
    a1i
    @6
    @2
    wi
    wph
    @6
    @0
    @1
    cS
    @5
    cG
    ulmscl
    cS
    @5
    cG
    ulmcl
    jca
    a1i
    wph
    @2
    @4
    @6
    wb
    wph
    @2
    wa
    #
    vz
    cv
    #
    vk
    cv
    #
    cF
    cfv
    #
    cfv
    #
    @8
    cG
    cfv
    #
    cmin
    co
    cabs
    cfv
    vr
    cv
    clt
    wbr
    vz
    cS
    wral
    #
    vk
    vj
    cv
    cuz
    cfv
    wral
    #
    vj
    cZ
    wrex
    #
    vr
    crp
    wral
    @14
    vj
    cW
    wrex
    #
    vr
    crp
    wral
    @4
    @6
    @7
    @15
    @16
    vr
    crp
    @7
    @15
    @14
    vj
    cz
    wrex
    #
    @16
    @7
    cM
    cz
    wcel
    #
    @15
    @17
    wb
    @7
    cN
    cM
    cuz
    cfv
    #
    wcel
    #
    @18
    wph
    @20
    @2
    wph
    cN
    cZ
    @19
    ulmres.m
    ulmres.z
    syl6eleq
    adantr
    #
    cM
    cN
    eluzel2
    syl
    #
    @13
    vj
    vk
    cM
    cZ
    ulmres.z
    rexuz3
    syl
    @7
    cN
    cz
    wcel
    #
    @16
    @17
    wb
    @7
    @20
    @23
    @21
    cM
    cN
    eluzelz
    syl
    #
    @13
    vj
    vk
    cN
    cW
    ulmres.w
    rexuz3
    syl
    bitr4d
    ralbidv
    @7
    vr
    vz
    @12
    @11
    cS
    vj
    vk
    cF
    cG
    cM
    cvv
    cZ
    ulmres.z
    @22
    wph
    cZ
    cc
    cS
    cmap
    co
    #
    cF
    wf
    @2
    ulmres.f
    adantr
    #
    @7
    @9
    cZ
    wcel
    @8
    cS
    wcel
    #
    wa
    wa
    @11
    eqidd
    @7
    @27
    wa
    @12
    eqidd
    #
    wph
    @0
    @1
    simprr
    #
    wph
    @0
    @1
    simprl
    #
    ulm2
    @7
    vr
    vz
    @12
    @11
    cS
    vj
    vk
    @5
    cG
    cN
    cvv
    cW
    ulmres.w
    @24
    @7
    cZ
    @25
    cW
    cF
    @26
    @7
    cN
    cuz
    cfv
    #
    @19
    cW
    cZ
    @7
    @20
    @31
    @19
    wss
    @21
    cM
    cN
    uzss
    syl
    ulmres.w
    ulmres.z
    3sstr4g
    fssresd
    @7
    @9
    cW
    wcel
    #
    @27
    wa
    wa
    @8
    @9
    @5
    cfv
    #
    @10
    @32
    @33
    @10
    wceq
    @7
    @27
    @9
    cW
    cF
    fvres
    ad2antrl
    fveq1d
    @28
    @29
    @30
    ulm2
    3bitr4d
    ex
    pm5.21ndd
end
