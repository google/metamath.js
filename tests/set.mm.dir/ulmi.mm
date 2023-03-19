include "crp.mm"
include "wcel.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "cv.mm"
include "clt.mm"
include "wbr.mm"
include "wral.mm"
include "cuz.mm"
include "wrex.mm"
include "culm.mm"
include "cvv.mm"
include "cc.mm"
include "wf.mm"
include "ulmcl.mm"
include "syl.mm"
include "ulmscl.mm"
include "ulm2.mm"
include "mpbid.mm"
include "wceq.mm"
include "breq2.mm"
include "ralbidv.mm"
include "rexralbidv.mm"
include "rspcv.mm"
include "sylc.mm"

theorem ulmi
  let wph: wff ph
  let vz: setvar z
  let cA: class A
  let cB: class B
  let cC: class C
  let cS: class S
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cM: class M
  let cZ: class Z
  let vn: setvar n
  let vx: setvar x
  let cV: class V
  assume ulm2.z: |- Z = ( ZZ>= ` M )
  assume ulm2.m: |- ( ph -> M e. ZZ )
  assume ulm2.f: |- ( ph -> F : Z --> ( CC ^m S ) )
  assume ulm2.b: |- ( ( ph /\ ( k e. Z /\ z e. S ) ) -> ( ( F ` k ) ` z ) = B )
  assume ulm2.a: |- ( ( ph /\ z e. S ) -> ( G ` z ) = A )
  assume ulmi.u: |- ( ph -> F ( ~~>u ` S ) G )
  assume ulmi.c: |- ( ph -> C e. RR+ )

  disjoint j k
  disjoint j z
  disjoint F j
  disjoint k z
  disjoint F k
  disjoint F z
  disjoint G j
  disjoint G k
  disjoint G z
  disjoint M j
  disjoint M k
  disjoint M z
  disjoint j ph
  disjoint k ph
  disjoint ph z
  disjoint A j
  disjoint A k
  disjoint C j
  disjoint C k
  disjoint C z
  disjoint S j
  disjoint S k
  disjoint S z
  disjoint Z j
  disjoint j n
  disjoint j x
  disjoint k n
  disjoint k x
  disjoint n x
  disjoint n z
  disjoint F n
  disjoint x z
  disjoint F x
  disjoint G n
  disjoint G x
  disjoint M n
  disjoint M x
  disjoint n ph
  disjoint ph x
  disjoint A n
  disjoint A x
  disjoint B n
  disjoint B x
  disjoint C x
  disjoint S n
  disjoint S x
  disjoint V n
  disjoint Z n
  disjoint Z x
  assert |- ( ph -> E. j e. Z A. k e. ( ZZ>= ` j ) A. z e. S ( abs ` ( B - A ) ) < C )

  proof
    wph
    cC
    crp
    wcel
    cB
    cA
    cmin
    co
    cabs
    cfv
    #
    vx
    cv
    #
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
    vj
    cZ
    wrex
    #
    vx
    crp
    wral
    #
    @0
    cC
    clt
    wbr
    #
    vz
    cS
    wral
    #
    vk
    @4
    wral
    vj
    cZ
    wrex
    #
    ulmi.c
    wph
    cF
    cG
    cS
    culm
    cfv
    wbr
    #
    @6
    ulmi.u
    wph
    vx
    vz
    cA
    cB
    cS
    vj
    vk
    cF
    cG
    cM
    cvv
    cZ
    ulm2.z
    ulm2.m
    ulm2.f
    ulm2.b
    ulm2.a
    wph
    @10
    cS
    cc
    cG
    wf
    ulmi.u
    cS
    cF
    cG
    ulmcl
    syl
    wph
    @10
    cS
    cvv
    wcel
    ulmi.u
    cS
    cF
    cG
    ulmscl
    syl
    ulm2
    mpbid
    @5
    @9
    vx
    cC
    crp
    @1
    cC
    wceq
    #
    @3
    @8
    vj
    vk
    cZ
    @4
    @11
    @2
    @7
    vz
    cS
    @1
    cC
    @0
    clt
    breq2
    ralbidv
    rexralbidv
    rspcv
    sylc
end
