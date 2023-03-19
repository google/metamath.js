include "cdv.mm"
include "co.mm"
include "cc.mm"
include "wf.mm"
include "wfn.mm"
include "cdm.mm"
include "cr.mm"
include "cpr.mm"
include "wcel.mm"
include "dvfg.mm"
include "syl.mm"
include "wss.mm"
include "recnprss.mm"
include "wral.mm"
include "cuz.mm"
include "cfv.mm"
include "cz.mm"
include "uzid.mm"
include "syl6eleqr.mm"
include "cv.mm"
include "wa.mm"
include "ulmdvlem2.mm"
include "dvbsss.mm"
include "syl6eqssr.mm"
include "ralrimiva.mm"
include "wceq.mm"
include "biidd.mm"
include "rspcv.mm"
include "sylc.mm"
include "dvbss.mm"
include "wbr.mm"
include "ulmdvlem3.mm"
include "vex.mm"
include "fvex.mm"
include "breldm.mm"
include "ex.mm"
include "ssrdv.mm"
include "eqssd.mm"
include "feq2d.mm"
include "mpbid.mm"
include "ffn.mm"
include "cmpt.mm"
include "culm.mm"
include "ulmcl.mm"
include "wfun.mm"
include "ffun.mm"
include "adantr.mm"
include "funbrfv.mm"
include "eqfnfvd.mm"

theorem ulmdv
  let wph: wff ph
  let vz: setvar z
  let cS: class S
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cH: class H
  let cM: class M
  let cX: class X
  let cZ: class Z
  let vj: setvar j
  let vm: setvar m
  let vn: setvar n
  let vs: setvar s
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vr: setvar r
  let cN: class N
  let cC: class C
  let wps: wff ps
  let cU: class U
  let cR: class R
  let cY: class Y
  assume ulmdv.z: |- Z = ( ZZ>= ` M )
  assume ulmdv.s: |- ( ph -> S e. { RR , CC } )
  assume ulmdv.m: |- ( ph -> M e. ZZ )
  assume ulmdv.f: |- ( ph -> F : Z --> ( CC ^m X ) )
  assume ulmdv.g: |- ( ph -> G : X --> CC )
  assume ulmdv.l: |- ( ( ph /\ z e. X ) -> ( k e. Z |-> ( ( F ` k ) ` z ) ) ~~> ( G ` z ) )
  assume ulmdv.u: |- ( ph -> ( k e. Z |-> ( S _D ( F ` k ) ) ) ( ~~>u ` X ) H )

  disjoint k z
  disjoint F k
  disjoint F z
  disjoint G z
  disjoint H z
  disjoint M k
  disjoint k ph
  disjoint ph z
  disjoint S k
  disjoint S z
  disjoint X k
  disjoint X z
  disjoint Z k
  disjoint Z z
  disjoint j k
  disjoint j m
  disjoint j n
  disjoint j s
  disjoint j u
  disjoint j v
  disjoint j w
  disjoint j x
  disjoint j y
  disjoint j z
  disjoint F j
  disjoint k m
  disjoint k n
  disjoint k s
  disjoint k u
  disjoint k v
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint m n
  disjoint m s
  disjoint m u
  disjoint m v
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint F m
  disjoint n s
  disjoint n u
  disjoint n v
  disjoint n w
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint F n
  disjoint s u
  disjoint s v
  disjoint s w
  disjoint s x
  disjoint s y
  disjoint s z
  disjoint F s
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u y
  disjoint u z
  disjoint F u
  disjoint v w
  disjoint v x
  disjoint v y
  disjoint v z
  disjoint F v
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint x y
  disjoint x z
  disjoint F x
  disjoint y z
  disjoint F y
  disjoint n r
  disjoint G n
  disjoint r s
  disjoint r u
  disjoint r v
  disjoint r w
  disjoint r y
  disjoint r z
  disjoint G r
  disjoint G s
  disjoint G u
  disjoint G v
  disjoint G w
  disjoint G y
  disjoint N k
  disjoint N m
  disjoint N n
  disjoint N w
  disjoint N x
  disjoint N y
  disjoint C k
  disjoint C n
  disjoint C y
  disjoint C z
  disjoint j r
  disjoint H j
  disjoint H n
  disjoint H r
  disjoint H s
  disjoint H u
  disjoint H v
  disjoint H w
  disjoint H y
  disjoint M j
  disjoint M n
  disjoint M x
  disjoint n ps
  disjoint ps w
  disjoint ps y
  disjoint j ph
  disjoint k r
  disjoint m r
  disjoint m ph
  disjoint n ph
  disjoint r x
  disjoint ph r
  disjoint ph s
  disjoint ph u
  disjoint ph v
  disjoint ph w
  disjoint ph x
  disjoint ph y
  disjoint S j
  disjoint S m
  disjoint S n
  disjoint S s
  disjoint S u
  disjoint S v
  disjoint S w
  disjoint S x
  disjoint S y
  disjoint U y
  disjoint R m
  disjoint R n
  disjoint R x
  disjoint R y
  disjoint X j
  disjoint X m
  disjoint X n
  disjoint X r
  disjoint X s
  disjoint X u
  disjoint X v
  disjoint X w
  disjoint X x
  disjoint X y
  disjoint Y k
  disjoint Y n
  disjoint Y y
  disjoint Y z
  disjoint Z j
  disjoint Z m
  disjoint Z n
  disjoint Z s
  disjoint Z u
  disjoint Z v
  disjoint Z w
  disjoint Z x
  disjoint Z y
  assert |- ( ph -> ( S _D G ) = H )

  proof
    wph
    vz
    cX
    cS
    cG
    cdv
    co
    #
    cH
    wph
    cX
    cc
    @0
    wf
    #
    @0
    cX
    wfn
    wph
    @0
    cdm
    #
    cc
    @0
    wf
    #
    @1
    wph
    cS
    cr
    cc
    cpr
    wcel
    #
    @3
    ulmdv.s
    cS
    cG
    dvfg
    syl
    #
    wph
    @2
    cX
    cc
    @0
    wph
    @2
    cX
    wph
    cX
    cS
    cG
    wph
    @4
    cS
    cc
    wss
    ulmdv.s
    cS
    recnprss
    syl
    ulmdv.g
    wph
    cM
    cZ
    wcel
    cX
    cS
    wss
    #
    vk
    cZ
    wral
    @6
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
    cM
    @7
    wcel
    ulmdv.m
    cM
    uzid
    syl
    ulmdv.z
    syl6eleqr
    wph
    @6
    vk
    cZ
    wph
    vk
    cv
    #
    cZ
    wcel
    wa
    cX
    cS
    @8
    cF
    cfv
    #
    cdv
    co
    #
    cdm
    cS
    wph
    vz
    cS
    vk
    cF
    cG
    cH
    cM
    cX
    cZ
    ulmdv.z
    ulmdv.s
    ulmdv.m
    ulmdv.f
    ulmdv.g
    ulmdv.l
    ulmdv.u
    ulmdvlem2
    cS
    @9
    dvbsss
    syl6eqssr
    ralrimiva
    @6
    @6
    vk
    cM
    cZ
    @8
    cM
    wceq
    @6
    biidd
    rspcv
    sylc
    dvbss
    wph
    vz
    cX
    @2
    wph
    vz
    cv
    #
    cX
    wcel
    #
    @11
    @2
    wcel
    #
    wph
    @12
    wa
    #
    @11
    @11
    cH
    cfv
    #
    @0
    wbr
    #
    @13
    wph
    vz
    cS
    vk
    cF
    cG
    cH
    cM
    cX
    cZ
    ulmdv.z
    ulmdv.s
    ulmdv.m
    ulmdv.f
    ulmdv.g
    ulmdv.l
    ulmdv.u
    ulmdvlem3
    #
    @11
    @15
    @0
    vz
    vex
    @11
    cH
    fvex
    breldm
    syl
    ex
    ssrdv
    eqssd
    feq2d
    mpbid
    cX
    cc
    @0
    ffn
    syl
    wph
    cX
    cc
    cH
    wf
    #
    cH
    cX
    wfn
    wph
    vk
    cZ
    @10
    cmpt
    #
    cH
    cX
    culm
    cfv
    wbr
    @18
    ulmdv.u
    cX
    @19
    cH
    ulmcl
    syl
    cX
    cc
    cH
    ffn
    syl
    @14
    @0
    wfun
    #
    @16
    @11
    @0
    cfv
    @15
    wceq
    wph
    @20
    @12
    wph
    @3
    @20
    @5
    @2
    cc
    @0
    ffun
    syl
    adantr
    @17
    @11
    @15
    @0
    funbrfv
    sylc
    eqfnfvd
end
