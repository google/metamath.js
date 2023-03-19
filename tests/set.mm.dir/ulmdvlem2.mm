include "cv.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cdv.mm"
include "co.mm"
include "cc.mm"
include "cmap.mm"
include "wf.mm"
include "cdm.mm"
include "wceq.mm"
include "cmpt.mm"
include "wral.mm"
include "wfn.mm"
include "culm.mm"
include "wbr.mm"
include "cvv.mm"
include "ovex.mm"
include "rgenw.mm"
include "eqid.mm"
include "fnmpt.mm"
include "mp1i.mm"
include "ulmf2.mm"
include "syl2anc.mm"
include "fmpt.mm"
include "sylibr.mm"
include "r19.21bi.mm"
include "elmapi.mm"
include "fdm.mm"
include "3syl.mm"

theorem ulmdvlem2
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
  assert |- ( ( ph /\ k e. Z ) -> dom ( S _D ( F ` k ) ) = X )

  proof
    wph
    vk
    cv
    #
    cZ
    wcel
    wa
    cS
    @0
    cF
    cfv
    #
    cdv
    co
    #
    cc
    cX
    cmap
    co
    #
    wcel
    #
    cX
    cc
    @2
    wf
    @2
    cdm
    cX
    wceq
    wph
    @4
    vk
    cZ
    wph
    cZ
    @3
    vk
    cZ
    @2
    cmpt
    #
    wf
    #
    @4
    vk
    cZ
    wral
    wph
    @5
    cZ
    wfn
    #
    @5
    cH
    cX
    culm
    cfv
    wbr
    @6
    @2
    cvv
    wcel
    #
    vk
    cZ
    wral
    @7
    wph
    @8
    vk
    cZ
    cS
    @1
    cdv
    ovex
    rgenw
    vk
    cZ
    @2
    @5
    cvv
    @5
    eqid
    #
    fnmpt
    mp1i
    ulmdv.u
    cX
    @5
    cH
    cZ
    ulmf2
    syl2anc
    vk
    cZ
    @3
    @2
    @5
    @9
    fmpt
    sylibr
    r19.21bi
    @2
    cc
    cX
    elmapi
    cX
    cc
    @2
    fdm
    3syl
end
