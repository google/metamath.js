include "cv.mm"
include "cfl.mm"
include "cfv.mm"
include "cfz.mm"
include "co.mm"
include "csu.mm"
include "cmin.mm"
include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "fzfid.mm"
include "wral.mm"
include "ralrimiva.mm"
include "adantr.mm"
include "cuz.mm"
include "elfzuz.mm"
include "syl6eleqr.mm"
include "weq.mm"
include "eleq1d.mm"
include "rspccva.mm"
include "syl2an.mm"
include "fsumrecl.mm"
include "resubcld.mm"
include "fmptd.mm"

theorem dvfsumrlimf
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cS: class S
  let cT: class T
  let vk: setvar k
  let cG: class G
  let cM: class M
  let cV: class V
  let cZ: class Z
  let vy: setvar y
  let vz: setvar z
  let vc: setvar c
  let ve: setvar e
  let vm: setvar m
  let cE: class E
  let cH: class H
  let cL: class L
  let vu: setvar u
  let vv: setvar v
  let vw: setvar w
  let cY: class Y
  let cU: class U
  let cX: class X
  assume dvfsum.s: |- S = ( T (,) +oo )
  assume dvfsum.z: |- Z = ( ZZ>= ` M )
  assume dvfsum.m: |- ( ph -> M e. ZZ )
  assume dvfsum.d: |- ( ph -> D e. RR )
  assume dvfsum.md: |- ( ph -> M <_ ( D + 1 ) )
  assume dvfsum.t: |- ( ph -> T e. RR )
  assume dvfsum.a: |- ( ( ph /\ x e. S ) -> A e. RR )
  assume dvfsum.b1: |- ( ( ph /\ x e. S ) -> B e. V )
  assume dvfsum.b2: |- ( ( ph /\ x e. Z ) -> B e. RR )
  assume dvfsum.b3: |- ( ph -> ( RR _D ( x e. S |-> A ) ) = ( x e. S |-> B ) )
  assume dvfsum.c: |- ( x = k -> B = C )
  assume dvfsumrlimf.g: |- G = ( x e. S |-> ( sum_ k e. ( M ... ( |_ ` x ) ) C - A ) )

  disjoint B k
  disjoint C x
  disjoint k x
  disjoint D k
  disjoint D x
  disjoint k ph
  disjoint ph x
  disjoint S k
  disjoint S x
  disjoint M k
  disjoint M x
  disjoint T x
  disjoint Z x
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint c e
  disjoint c k
  disjoint c m
  disjoint c y
  disjoint c z
  disjoint B c
  disjoint e k
  disjoint e m
  disjoint e y
  disjoint e z
  disjoint B e
  disjoint k m
  disjoint k y
  disjoint k z
  disjoint m y
  disjoint m z
  disjoint B m
  disjoint B y
  disjoint B z
  disjoint x z
  disjoint C z
  disjoint c x
  disjoint D c
  disjoint x y
  disjoint D y
  disjoint E x
  disjoint E y
  disjoint G c
  disjoint G e
  disjoint G y
  disjoint G z
  disjoint H m
  disjoint H y
  disjoint H z
  disjoint c ph
  disjoint e x
  disjoint e ph
  disjoint m x
  disjoint m ph
  disjoint ph y
  disjoint S c
  disjoint S e
  disjoint S m
  disjoint S y
  disjoint S z
  disjoint L y
  disjoint M z
  disjoint c u
  disjoint c v
  disjoint c w
  disjoint T c
  disjoint u v
  disjoint u w
  disjoint u x
  disjoint u z
  disjoint T u
  disjoint v w
  disjoint v x
  disjoint v z
  disjoint T v
  disjoint w x
  disjoint w z
  disjoint T w
  disjoint T z
  disjoint Y k
  disjoint Y m
  disjoint Y x
  disjoint Y y
  disjoint Y z
  disjoint U k
  disjoint U x
  disjoint k u
  disjoint k v
  disjoint k w
  disjoint X k
  disjoint m u
  disjoint m v
  disjoint m w
  disjoint X m
  disjoint u y
  disjoint X u
  disjoint v y
  disjoint X v
  disjoint w y
  disjoint X w
  disjoint X x
  disjoint X y
  disjoint X z
  assert |- ( ph -> G : S --> RR )

  proof
    wph
    vx
    cS
    cM
    vx
    cv
    #
    cfl
    cfv
    #
    cfz
    co
    #
    cC
    vk
    csu
    #
    cA
    cmin
    co
    cr
    cG
    wph
    @0
    cS
    wcel
    #
    wa
    #
    @3
    cA
    @5
    @2
    cC
    vk
    @5
    cM
    @1
    fzfid
    @5
    cB
    cr
    wcel
    #
    vx
    cZ
    wral
    #
    vk
    cv
    #
    cZ
    wcel
    cC
    cr
    wcel
    #
    @8
    @2
    wcel
    #
    wph
    @7
    @4
    wph
    @6
    vx
    cZ
    dvfsum.b2
    ralrimiva
    adantr
    @10
    @8
    cM
    cuz
    cfv
    cZ
    @8
    cM
    @1
    elfzuz
    dvfsum.z
    syl6eleqr
    @6
    @9
    vx
    @8
    cZ
    vx
    vk
    weq
    cB
    cC
    cr
    dvfsum.c
    eleq1d
    rspccva
    syl2an
    fsumrecl
    dvfsum.a
    resubcld
    dvfsumrlimf.g
    fmptd
end
