include "cv.mm"
include "cfv.mm"
include "cc.mm"
include "wcel.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cuz.mm"
include "wral.mm"
include "wrex.mm"
include "crp.mm"
include "wb.mm"
include "wtru.mm"
include "cz.mm"
include "uzssz.mm"
include "eqsstri.mm"
include "id.mm"
include "eleq1.mm"
include "wceq.mm"
include "abssub.mm"
include "3adant1.mm"
include "cr.mm"
include "c2.mm"
include "cdiv.mm"
include "wi.mm"
include "abs3lem.mm"
include "cau3lem.mm"
include "trud.mm"

theorem cau3
  let vx: setvar x
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let cF: class F
  let cM: class M
  let cZ: class Z
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let cN: class N
  let cW: class W
  assume cau3.1: |- Z = ( ZZ>= ` M )

  disjoint j k
  disjoint j m
  disjoint j x
  disjoint F j
  disjoint k m
  disjoint k x
  disjoint F k
  disjoint m x
  disjoint F m
  disjoint F x
  disjoint M j
  disjoint M k
  disjoint M x
  disjoint Z j
  disjoint Z k
  disjoint Z x
  disjoint j w
  disjoint j y
  disjoint j z
  disjoint k w
  disjoint k y
  disjoint k z
  disjoint m w
  disjoint m y
  disjoint m z
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
  disjoint N j
  disjoint N k
  disjoint N x
  disjoint Z w
  disjoint Z y
  disjoint Z z
  disjoint W j
  disjoint W k
  disjoint W x
  assert |- ( A. x e. RR+ E. j e. Z A. k e. ( ZZ>= ` j ) ( ( F ` k ) e. CC /\ ( abs ` ( ( F ` k ) - ( F ` j ) ) ) < x ) <-> A. x e. RR+ E. j e. Z A. k e. ( ZZ>= ` j ) ( ( F ` k ) e. CC /\ A. m e. ( ZZ>= ` k ) ( abs ` ( ( F ` k ) - ( F ` m ) ) ) < x ) )

  proof
    vk
    cv
    #
    cF
    cfv
    #
    cc
    wcel
    #
    @1
    vj
    cv
    #
    cF
    cfv
    #
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
    wa
    vk
    @3
    cuz
    cfv
    #
    wral
    vj
    cZ
    wrex
    vx
    crp
    wral
    @2
    @1
    vm
    cv
    cF
    cfv
    #
    cmin
    co
    cabs
    cfv
    @6
    clt
    wbr
    #
    vm
    @0
    cuz
    cfv
    wral
    wa
    vk
    @7
    wral
    vj
    cZ
    wrex
    vx
    crp
    wral
    wb
    wtru
    @2
    @4
    cc
    wcel
    #
    @8
    cc
    wcel
    #
    @2
    vx
    cmin
    vj
    vk
    vm
    cF
    cabs
    cZ
    cZ
    cM
    cuz
    cfv
    cz
    cau3.1
    cM
    uzssz
    eqsstri
    @2
    id
    @1
    @4
    cc
    eleq1
    @1
    @8
    cc
    eleq1
    @10
    @2
    @4
    @1
    cmin
    co
    cabs
    cfv
    @5
    wceq
    wtru
    @4
    @1
    abssub
    3adant1
    @11
    @10
    @8
    @4
    cmin
    co
    cabs
    cfv
    @4
    @8
    cmin
    co
    cabs
    cfv
    #
    wceq
    wtru
    @8
    @4
    abssub
    3adant1
    @2
    @11
    wa
    @10
    @6
    cr
    wcel
    wa
    @5
    @6
    c2
    cdiv
    co
    #
    clt
    wbr
    @12
    @13
    clt
    wbr
    wa
    @9
    wi
    wtru
    @1
    @8
    @4
    @6
    abs3lem
    3adant1
    cau3lem
    trud
end
