include "ccnfld.mm"
include "cv.mm"
include "csn.mm"
include "cun.mm"
include "cres.mm"
include "cgsu.mm"
include "co.mm"
include "cfv.mm"
include "caddc.mm"
include "cmpt.mm"
include "cc.mm"
include "cnfldbas.mm"
include "cnfldadd.mm"
include "crg.mm"
include "wcel.mm"
include "ccmn.mm"
include "cnring.mm"
include "ringcmn.mm"
include "mp1i.mm"
include "cfn.mm"
include "wss.mm"
include "unssad.mm"
include "ssfi.mm"
include "syl2anc.mm"
include "wa.mm"
include "cc0.mm"
include "cpnf.mm"
include "cico.mm"
include "cr.mm"
include "rge0ssre.mm"
include "ax-resscn.mm"
include "sstri.mm"
include "sselda.mm"
include "ffvelrnda.mm"
include "syldan.mm"
include "sseldi.mm"
include "unssbd.mm"
include "vex.mm"
include "snss.mm"
include "sylibr.mm"
include "ffvelrnd.mm"
include "fveq2.mm"
include "gsumunsn.mm"
include "feqresmpt.mm"
include "oveq2d.mm"
include "oveq1d.mm"
include "3eqtr4d.mm"
include "oveq1i.mm"
include "3eqtr4g.mm"

theorem jensenlem1
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vt: setvar t
  let cA: class A
  let cB: class B
  let cD: class D
  let cS: class S
  let cT: class T
  let cF: class F
  let cL: class L
  let cX: class X
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let vk: setvar k
  let vw: setvar w
  assume jensen.1: |- ( ph -> D C_ RR )
  assume jensen.2: |- ( ph -> F : D --> RR )
  assume jensen.3: |- ( ( ph /\ ( a e. D /\ b e. D ) ) -> ( a [,] b ) C_ D )
  assume jensen.4: |- ( ph -> A e. Fin )
  assume jensen.5: |- ( ph -> T : A --> ( 0 [,) +oo ) )
  assume jensen.6: |- ( ph -> X : A --> D )
  assume jensen.7: |- ( ph -> 0 < ( CCfld gsum T ) )
  assume jensen.8: |- ( ( ph /\ ( x e. D /\ y e. D /\ t e. ( 0 [,] 1 ) ) ) -> ( F ` ( ( t x. x ) + ( ( 1 - t ) x. y ) ) ) <_ ( ( t x. ( F ` x ) ) + ( ( 1 - t ) x. ( F ` y ) ) ) )
  assume jensenlem.1: |- ( ph -> -. z e. B )
  assume jensenlem.2: |- ( ph -> ( B u. { z } ) C_ A )
  assume jensenlem.s: |- S = ( CCfld gsum ( T |` B ) )
  assume jensenlem.l: |- L = ( CCfld gsum ( T |` ( B u. { z } ) ) )

  disjoint a b
  disjoint a t
  disjoint a x
  disjoint a y
  disjoint A a
  disjoint b t
  disjoint b x
  disjoint b y
  disjoint A b
  disjoint t x
  disjoint t y
  disjoint A t
  disjoint x y
  disjoint A x
  disjoint A y
  disjoint D a
  disjoint D b
  disjoint D t
  disjoint D x
  disjoint D y
  disjoint a ph
  disjoint b ph
  disjoint ph t
  disjoint ph x
  disjoint ph y
  disjoint F a
  disjoint F b
  disjoint F t
  disjoint F x
  disjoint F y
  disjoint T a
  disjoint T b
  disjoint T t
  disjoint T x
  disjoint T y
  disjoint X a
  disjoint X b
  disjoint X t
  disjoint X x
  disjoint X y
  disjoint a z
  disjoint B a
  disjoint b z
  disjoint B b
  disjoint t z
  disjoint B t
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint L t
  disjoint L x
  disjoint L y
  disjoint S a
  disjoint S b
  disjoint S t
  disjoint S x
  disjoint S y
  disjoint a c
  disjoint a k
  disjoint a w
  disjoint b c
  disjoint b k
  disjoint b w
  disjoint c k
  disjoint c t
  disjoint c w
  disjoint c x
  disjoint c y
  disjoint A c
  disjoint k t
  disjoint k w
  disjoint k x
  disjoint k y
  disjoint A k
  disjoint t w
  disjoint w x
  disjoint w y
  disjoint A w
  disjoint D c
  disjoint D k
  disjoint D w
  disjoint c ph
  disjoint k ph
  disjoint ph w
  disjoint F c
  disjoint F k
  disjoint F w
  disjoint T c
  disjoint T k
  disjoint T w
  disjoint X c
  disjoint X k
  disjoint X w
  assert |- ( ph -> L = ( S + ( T ` z ) ) )

  proof
    wph
    ccnfld
    cT
    cB
    vz
    cv
    #
    csn
    #
    cun
    #
    cres
    #
    cgsu
    co
    #
    ccnfld
    cT
    cB
    cres
    #
    cgsu
    co
    #
    @0
    cT
    cfv
    #
    caddc
    co
    #
    cL
    cS
    @7
    caddc
    co
    wph
    ccnfld
    vx
    @2
    vx
    cv
    #
    cT
    cfv
    #
    cmpt
    #
    cgsu
    co
    ccnfld
    vx
    cB
    @10
    cmpt
    #
    cgsu
    co
    #
    @7
    caddc
    co
    @4
    @8
    wph
    cB
    cc
    caddc
    vx
    ccnfld
    @0
    cA
    @10
    @7
    cnfldbas
    cnfldadd
    ccnfld
    crg
    wcel
    ccnfld
    ccmn
    wcel
    wph
    cnring
    ccnfld
    ringcmn
    mp1i
    wph
    cA
    cfn
    wcel
    cB
    cA
    wss
    cB
    cfn
    wcel
    jensen.4
    wph
    cB
    @1
    cA
    jensenlem.2
    unssad
    #
    cA
    cB
    ssfi
    syl2anc
    wph
    @9
    cB
    wcel
    #
    wa
    cc0
    cpnf
    cico
    co
    #
    cc
    @10
    @16
    cr
    cc
    rge0ssre
    ax-resscn
    sstri
    #
    wph
    @15
    @9
    cA
    wcel
    @10
    @16
    wcel
    wph
    cB
    cA
    @9
    @14
    sselda
    wph
    cA
    @16
    @9
    cT
    jensen.5
    ffvelrnda
    syldan
    sseldi
    wph
    @1
    cA
    wss
    @0
    cA
    wcel
    wph
    cB
    @1
    cA
    jensenlem.2
    unssbd
    @0
    cA
    vz
    vex
    snss
    sylibr
    #
    jensenlem.1
    wph
    @16
    cc
    @7
    @17
    wph
    cA
    @16
    @0
    cT
    jensen.5
    @18
    ffvelrnd
    sseldi
    @9
    @0
    cT
    fveq2
    gsumunsn
    wph
    @3
    @11
    ccnfld
    cgsu
    wph
    vx
    cA
    @16
    @2
    cT
    jensen.5
    jensenlem.2
    feqresmpt
    oveq2d
    wph
    @6
    @13
    @7
    caddc
    wph
    @5
    @12
    ccnfld
    cgsu
    wph
    vx
    cA
    @16
    cB
    cT
    jensen.5
    @14
    feqresmpt
    oveq2d
    oveq1d
    3eqtr4d
    jensenlem.l
    cS
    @6
    @7
    caddc
    jensenlem.s
    oveq1i
    3eqtr4g
end
