include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "cc.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "clt.mm"
include "wbr.mm"
include "cuz.mm"
include "wral.mm"
include "wa.mm"
include "wrex.mm"
include "crp.mm"
include "wb.mm"
include "cz.mm"
include "eluzel2.mm"
include "rexuz3.mm"
include "syl.mm"
include "eluzelz.mm"
include "bitr4d.mm"
include "eleq2s.mm"
include "ralbidv.mm"
include "cau3.mm"
include "3bitr4g.mm"

theorem cau4
  let vx: setvar x
  let vj: setvar j
  let vk: setvar k
  let cF: class F
  let cM: class M
  let cN: class N
  let cW: class W
  let cZ: class Z
  let vm: setvar m
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  assume cau3.1: |- Z = ( ZZ>= ` M )
  assume cau4.2: |- W = ( ZZ>= ` N )

  disjoint j k
  disjoint j x
  disjoint F j
  disjoint k x
  disjoint F k
  disjoint F x
  disjoint M j
  disjoint M k
  disjoint M x
  disjoint N j
  disjoint N k
  disjoint N x
  disjoint Z j
  disjoint Z k
  disjoint Z x
  disjoint W j
  disjoint W k
  disjoint W x
  disjoint j m
  disjoint j w
  disjoint j y
  disjoint j z
  disjoint k m
  disjoint k w
  disjoint k y
  disjoint k z
  disjoint m w
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint F m
  disjoint w x
  disjoint w y
  disjoint w z
  disjoint F w
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint F y
  disjoint F z
  disjoint M w
  disjoint Z w
  disjoint Z y
  disjoint Z z
  assert |- ( N e. Z -> ( A. x e. RR+ E. j e. Z A. k e. ( ZZ>= ` j ) ( ( F ` k ) e. CC /\ ( abs ` ( ( F ` k ) - ( F ` j ) ) ) < x ) <-> A. x e. RR+ E. j e. W A. k e. ( ZZ>= ` j ) ( ( F ` k ) e. CC /\ ( abs ` ( ( F ` k ) - ( F ` j ) ) ) < x ) ) )

  proof
    cN
    cZ
    wcel
    #
    vk
    cv
    #
    cF
    cfv
    #
    cc
    wcel
    #
    @2
    vy
    cv
    cF
    cfv
    cmin
    co
    cabs
    cfv
    vx
    cv
    #
    clt
    wbr
    vy
    @1
    cuz
    cfv
    wral
    wa
    #
    vk
    vj
    cv
    #
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
    @8
    vj
    cW
    wrex
    #
    vx
    crp
    wral
    @3
    @2
    @6
    cF
    cfv
    cmin
    co
    cabs
    cfv
    @4
    clt
    wbr
    wa
    vk
    @7
    wral
    #
    vj
    cZ
    wrex
    vx
    crp
    wral
    @11
    vj
    cW
    wrex
    vx
    crp
    wral
    @0
    @9
    @10
    vx
    crp
    @9
    @10
    wb
    cN
    cM
    cuz
    cfv
    #
    cZ
    cN
    @12
    wcel
    #
    @9
    @8
    vj
    cz
    wrex
    #
    @10
    @13
    cM
    cz
    wcel
    @9
    @14
    wb
    cM
    cN
    eluzel2
    @5
    vj
    vk
    cM
    cZ
    cau3.1
    rexuz3
    syl
    @13
    cN
    cz
    wcel
    @10
    @14
    wb
    cM
    cN
    eluzelz
    @5
    vj
    vk
    cN
    cW
    cau4.2
    rexuz3
    syl
    bitr4d
    cau3.1
    eleq2s
    ralbidv
    vx
    vj
    vk
    vy
    cF
    cM
    cZ
    cau3.1
    cau3
    vx
    vj
    vk
    vy
    cF
    cN
    cW
    cau4.2
    cau3
    3bitr4g
end
