include "c0.mm"
include "wceq.mm"
include "wa.mm"
include "culm.mm"
include "cfv.mm"
include "wbr.mm"
include "cv.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "clt.mm"
include "wral.mm"
include "cuz.mm"
include "wrex.mm"
include "crp.mm"
include "wne.mm"
include "wcel.mm"
include "cz.mm"
include "uzid.mm"
include "syl.mm"
include "syl6eleqr.mm"
include "ne0i.mm"
include "adantr.mm"
include "ral0.mm"
include "simpr.mm"
include "raleqdv.mm"
include "mpbiri.mm"
include "ralrimivw.mm"
include "r19.2z.mm"
include "syl2anc.mm"
include "cvv.mm"
include "cc.mm"
include "cmap.mm"
include "wf.mm"
include "eqidd.mm"
include "0ex.mm"
include "syl6eqel.mm"
include "ulm2.mm"
include "mpbird.mm"

theorem ulm0
  let wph: wff ph
  let cS: class S
  let cF: class F
  let cG: class G
  let cM: class M
  let cZ: class Z
  let vj: setvar j
  let vk: setvar k
  let vx: setvar x
  let vz: setvar z
  assume ulm0.z: |- Z = ( ZZ>= ` M )
  assume ulm0.m: |- ( ph -> M e. ZZ )
  assume ulm0.f: |- ( ph -> F : Z --> ( CC ^m S ) )
  assume ulm0.g: |- ( ph -> G : S --> CC )


  assert |- ( ( ph /\ S = (/) ) -> F ( ~~>u ` S ) G )

  proof
    wph
    cS
    c0
    wceq
    #
    wa
    #
    cF
    cG
    cS
    culm
    cfv
    wbr
    vz
    cv
    #
    vk
    cv
    #
    cF
    cfv
    cfv
    #
    @2
    cG
    cfv
    #
    cmin
    co
    cabs
    cfv
    vx
    cv
    clt
    wbr
    #
    vz
    cS
    wral
    #
    vk
    vj
    cv
    cuz
    cfv
    #
    wral
    #
    vj
    cZ
    wrex
    #
    vx
    crp
    wral
    @1
    @10
    vx
    crp
    @1
    cZ
    c0
    wne
    #
    @9
    vj
    cZ
    wral
    @10
    wph
    @11
    @0
    wph
    cM
    cZ
    wcel
    @11
    wph
    cM
    cM
    cuz
    cfv
    #
    cZ
    wph
    cM
    cz
    wcel
    #
    cM
    @12
    wcel
    ulm0.m
    cM
    uzid
    syl
    ulm0.z
    syl6eleqr
    cZ
    cM
    ne0i
    syl
    adantr
    @1
    @9
    vj
    cZ
    @1
    @7
    vk
    @8
    @1
    @7
    @6
    vz
    c0
    wral
    @6
    vz
    ral0
    @1
    @6
    vz
    cS
    c0
    wph
    @0
    simpr
    #
    raleqdv
    mpbiri
    ralrimivw
    ralrimivw
    @9
    vj
    cZ
    r19.2z
    syl2anc
    ralrimivw
    @1
    vx
    vz
    @5
    @4
    cS
    vj
    vk
    cF
    cG
    cM
    cvv
    cZ
    ulm0.z
    wph
    @13
    @0
    ulm0.m
    adantr
    wph
    cZ
    cc
    cS
    cmap
    co
    cF
    wf
    @0
    ulm0.f
    adantr
    @1
    @3
    cZ
    wcel
    @2
    cS
    wcel
    #
    wa
    wa
    @4
    eqidd
    @1
    @15
    wa
    @5
    eqidd
    wph
    cS
    cc
    cG
    wf
    @0
    ulm0.g
    adantr
    @1
    cS
    c0
    cvv
    @14
    0ex
    syl6eqel
    ulm2
    mpbird
end
