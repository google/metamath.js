include "clm.mm"
include "cfv.mm"
include "wbr.mm"
include "cc.mm"
include "cpm.mm"
include "co.mm"
include "wcel.mm"
include "cv.mm"
include "cdm.mm"
include "clt.mm"
include "w3a.mm"
include "cuz.mm"
include "wral.mm"
include "cz.mm"
include "wrex.mm"
include "crp.mm"
include "lmmbr2.mm"
include "wb.mm"
include "rexuz3.mm"
include "syl.mm"
include "ralbidv.mm"
include "3anbi3d.mm"
include "bitr4d.mm"

theorem lmmbr3
  let wph: wff ph
  let vx: setvar x
  let cD: class D
  let cP: class P
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let cJ: class J
  let cM: class M
  let cX: class X
  let cZ: class Z
  let vu: setvar u
  let vy: setvar y
  let cR: class R
  assume lmmbr.2: |- J = ( MetOpen ` D )
  assume lmmbr.3: |- ( ph -> D e. ( *Met ` X ) )
  assume lmmbr3.5: |- Z = ( ZZ>= ` M )
  assume lmmbr3.6: |- ( ph -> M e. ZZ )

  disjoint j k
  disjoint j x
  disjoint D j
  disjoint k x
  disjoint D k
  disjoint D x
  disjoint F j
  disjoint F k
  disjoint F x
  disjoint P j
  disjoint P k
  disjoint P x
  disjoint X j
  disjoint X k
  disjoint X x
  disjoint J x
  disjoint M j
  disjoint j ph
  disjoint k ph
  disjoint ph x
  disjoint Z j
  disjoint Z k
  disjoint Z x
  disjoint j u
  disjoint j y
  disjoint k u
  disjoint k y
  disjoint u x
  disjoint u y
  disjoint D u
  disjoint x y
  disjoint D y
  disjoint F u
  disjoint F y
  disjoint P u
  disjoint P y
  disjoint X u
  disjoint X y
  disjoint J u
  disjoint J y
  disjoint ph u
  disjoint R j
  disjoint R k
  disjoint R x
  assert |- ( ph -> ( F ( ~~>t ` J ) P <-> ( F e. ( X ^pm CC ) /\ P e. X /\ A. x e. RR+ E. j e. Z A. k e. ( ZZ>= ` j ) ( k e. dom F /\ ( F ` k ) e. X /\ ( ( F ` k ) D P ) < x ) ) ) )

  proof
    wph
    cF
    cP
    cJ
    clm
    cfv
    wbr
    cF
    cX
    cc
    cpm
    co
    wcel
    #
    cP
    cX
    wcel
    #
    vk
    cv
    #
    cF
    cdm
    wcel
    @2
    cF
    cfv
    #
    cX
    wcel
    @3
    cP
    cD
    co
    vx
    cv
    clt
    wbr
    w3a
    #
    vk
    vj
    cv
    cuz
    cfv
    wral
    #
    vj
    cz
    wrex
    #
    vx
    crp
    wral
    #
    w3a
    @0
    @1
    @5
    vj
    cZ
    wrex
    #
    vx
    crp
    wral
    #
    w3a
    wph
    vx
    cD
    cP
    vj
    vk
    cF
    cJ
    cX
    lmmbr.2
    lmmbr.3
    lmmbr2
    wph
    @9
    @7
    @0
    @1
    wph
    @8
    @6
    vx
    crp
    wph
    cM
    cz
    wcel
    @8
    @6
    wb
    lmmbr3.6
    @4
    vj
    vk
    cM
    cZ
    lmmbr3.5
    rexuz3
    syl
    ralbidv
    3anbi3d
    bitr4d
end
