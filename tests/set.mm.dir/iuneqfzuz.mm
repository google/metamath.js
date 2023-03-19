include "cv.mm"
include "cfz.mm"
include "co.mm"
include "ciun.mm"
include "wceq.mm"
include "wral.mm"
include "iuneqfzuzlem.mm"
include "wss.mm"
include "eqcom.mm"
include "ralbii.mm"
include "biimpi.mm"
include "syl.mm"
include "eqssd.mm"

theorem iuneqfzuz
  let cA: class A
  let cB: class B
  let vm: setvar m
  let vn: setvar n
  let cN: class N
  let cZ: class Z
  assume iuneqfzuz.z: |- Z = ( ZZ>= ` N )

  disjoint A m
  disjoint B m
  disjoint N n
  disjoint Z m
  disjoint Z n
  disjoint m n
  assert |- ( A. m e. Z U_ n e. ( N ... m ) A = U_ n e. ( N ... m ) B -> U_ n e. Z A = U_ n e. Z B )

  proof
    vn
    cN
    vm
    cv
    cfz
    co
    #
    cA
    ciun
    #
    vn
    @0
    cB
    ciun
    #
    wceq
    #
    vm
    cZ
    wral
    #
    vn
    cZ
    cA
    ciun
    #
    vn
    cZ
    cB
    ciun
    #
    cA
    cB
    vm
    vn
    cN
    cZ
    iuneqfzuz.z
    iuneqfzuzlem
    @4
    @2
    @1
    wceq
    #
    vm
    cZ
    wral
    #
    @6
    @5
    wss
    @4
    @8
    @3
    @7
    vm
    cZ
    @1
    @2
    eqcom
    ralbii
    biimpi
    cB
    cA
    vm
    vn
    cN
    cZ
    iuneqfzuz.z
    iuneqfzuzlem
    syl
    eqssd
end
