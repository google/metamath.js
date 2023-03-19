include "cv.mm"
include "wcel.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cpnf.mm"
include "cico.mm"
include "co.mm"
include "cc0.mm"
include "cxr.mm"
include "wne.mm"
include "clt.mm"
include "csup.mm"
include "wceq.mm"
include "cr.mm"
include "cioo.mm"
include "ioossre.mm"
include "eqsstri.mm"
include "simprl.mm"
include "sseldi.mm"
include "rexrd.mm"
include "renepnfd.mm"
include "icopnfsup.mm"
include "syl2anc.mm"
include "wss.mm"
include "adantr.mm"
include "syl6eleq.mm"
include "wb.mm"
include "elioopnf.mm"
include "syl.mm"
include "mpbid.mm"
include "simprd.mm"
include "df-ioo.mm"
include "df-ico.mm"
include "xrltletr.mm"
include "ixxss1.mm"
include "syl6sseqr.mm"
include "cmpt.mm"
include "crli.mm"
include "cbvmptv.mm"
include "syl5eqbrr.mm"
include "rlimres2.mm"
include "cc.mm"
include "a1i.mm"
include "dvmptrecl.mm"
include "adantrr.mm"
include "recnd.mm"
include "rlimconst.mm"
include "sselda.mm"
include "wral.mm"
include "ralrimiva.mm"
include "eleq1d.mm"
include "rspccva.mm"
include "sylan.mm"
include "syldan.mm"
include "simpll.mm"
include "simplrl.mm"
include "simplrr.mm"
include "elicopnf.mm"
include "simplbda.mm"
include "syl122anc.mm"
include "rlimle.mm"

theorem dvfsumrlimge0
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
  assume dvfsumrlim.l: |- ( ( ph /\ ( x e. S /\ k e. S ) /\ ( D <_ x /\ x <_ k ) ) -> C <_ B )
  assume dvfsumrlim.g: |- G = ( x e. S |-> ( sum_ k e. ( M ... ( |_ ` x ) ) C - A ) )
  assume dvfsumrlim.k: |- ( ph -> ( x e. S |-> B ) ~~>r 0 )

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
  assert |- ( ( ph /\ ( x e. S /\ D <_ x ) ) -> 0 <_ B )

  proof
    wph
    vx
    cv
    #
    cS
    wcel
    #
    cD
    @0
    cle
    wbr
    #
    wa
    #
    wa
    #
    vk
    @0
    cpnf
    cico
    co
    #
    cC
    cB
    cc0
    cB
    @4
    @0
    cxr
    wcel
    @0
    cpnf
    wne
    @5
    cxr
    clt
    csup
    cpnf
    wceq
    @4
    @0
    @4
    cS
    cr
    @0
    cS
    cT
    cpnf
    cioo
    co
    #
    cr
    dvfsum.s
    cT
    cpnf
    ioossre
    eqsstri
    #
    wph
    @1
    @2
    simprl
    #
    sseldi
    #
    rexrd
    @4
    @0
    @9
    renepnfd
    @0
    icopnfsup
    syl2anc
    @4
    vk
    @5
    cS
    cC
    cc0
    @4
    @5
    @6
    cS
    @4
    cT
    cxr
    wcel
    #
    cT
    @0
    clt
    wbr
    #
    @5
    @6
    wss
    wph
    @10
    @3
    wph
    cT
    dvfsum.t
    rexrd
    adantr
    #
    @4
    @0
    cr
    wcel
    #
    @11
    @4
    @0
    @6
    wcel
    #
    @13
    @11
    wa
    #
    @4
    @0
    cS
    @6
    @8
    dvfsum.s
    syl6eleq
    @4
    @10
    @14
    @15
    wb
    @12
    cT
    @0
    elioopnf
    syl
    mpbid
    simprd
    vu
    vv
    vw
    vz
    cT
    @0
    cpnf
    cico
    clt
    clt
    cle
    cioo
    clt
    vu
    vv
    vw
    df-ioo
    vu
    vv
    vw
    df-ico
    cT
    @0
    vz
    cv
    xrltletr
    ixxss1
    syl2anc
    dvfsum.s
    syl6sseqr
    #
    @4
    vk
    cS
    cC
    cmpt
    vx
    cS
    cB
    cmpt
    #
    cc0
    crli
    vx
    vk
    cS
    cB
    cC
    dvfsum.c
    cbvmptv
    wph
    @17
    cc0
    crli
    wbr
    @3
    dvfsumrlim.k
    adantr
    syl5eqbrr
    rlimres2
    @4
    vk
    @5
    cS
    cB
    cB
    @16
    @4
    cS
    cr
    wss
    #
    cB
    cc
    wcel
    vk
    cS
    cB
    cmpt
    cB
    crli
    wbr
    @18
    @4
    @7
    a1i
    @4
    cB
    wph
    @1
    cB
    cr
    wcel
    #
    @2
    wph
    vx
    cA
    cB
    cS
    cV
    @18
    wph
    @7
    a1i
    dvfsum.a
    dvfsum.b1
    dvfsum.b3
    dvmptrecl
    #
    adantrr
    #
    recnd
    vk
    cS
    cB
    rlimconst
    syl2anc
    rlimres2
    @4
    vk
    cv
    #
    @5
    wcel
    #
    @22
    cS
    wcel
    #
    cC
    cr
    wcel
    #
    @4
    @5
    cS
    @22
    @16
    sselda
    #
    @4
    @19
    vx
    cS
    wral
    #
    @24
    @25
    wph
    @27
    @3
    wph
    @19
    vx
    cS
    @20
    ralrimiva
    adantr
    @19
    @25
    vx
    @22
    cS
    @0
    @22
    wceq
    cB
    cC
    cr
    dvfsum.c
    eleq1d
    rspccva
    sylan
    syldan
    @4
    @19
    @23
    @21
    adantr
    @4
    @23
    wa
    wph
    @1
    @24
    @2
    @0
    @22
    cle
    wbr
    #
    cC
    cB
    cle
    wbr
    wph
    @3
    @23
    simpll
    wph
    @1
    @2
    @23
    simplrl
    @26
    wph
    @1
    @2
    @23
    simplrr
    @4
    @23
    @22
    cr
    wcel
    #
    @28
    @4
    @13
    @23
    @29
    @28
    wa
    wb
    @9
    @0
    @22
    elicopnf
    syl
    simplbda
    dvfsumrlim.l
    syl122anc
    rlimle
end
