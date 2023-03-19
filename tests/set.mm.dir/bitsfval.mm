include "c2.mm"
include "cv.mm"
include "cexp.mm"
include "co.mm"
include "cdiv.mm"
include "cfl.mm"
include "cfv.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "cn0.mm"
include "crab.mm"
include "cz.mm"
include "cbits.mm"
include "wceq.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "breq2d.mm"
include "notbid.mm"
include "rabbidv.mm"
include "df-bits.mm"
include "nn0ex.mm"
include "rabex.mm"
include "fvmpt.mm"

theorem bitsfval
  let vm: setvar m
  let cN: class N
  let vk: setvar k
  let vn: setvar n
  let cM: class M

  disjoint N m
  disjoint k n
  disjoint M m
  disjoint m n
  disjoint N n
  assert |- ( N e. ZZ -> ( bits ` N ) = { m e. NN0 | -. 2 || ( |_ ` ( N / ( 2 ^ m ) ) ) } )

  proof
    vn
    cN
    c2
    vn
    cv
    #
    c2
    vm
    cv
    cexp
    co
    #
    cdiv
    co
    #
    cfl
    cfv
    #
    cdvds
    wbr
    #
    wn
    #
    vm
    cn0
    crab
    c2
    cN
    @1
    cdiv
    co
    #
    cfl
    cfv
    #
    cdvds
    wbr
    #
    wn
    #
    vm
    cn0
    crab
    cz
    cbits
    @0
    cN
    wceq
    #
    @5
    @9
    vm
    cn0
    @10
    @4
    @8
    @10
    @3
    @7
    c2
    cdvds
    @10
    @2
    @6
    cfl
    @0
    cN
    @1
    cdiv
    oveq1
    fveq2d
    breq2d
    notbid
    rabbidv
    vm
    vn
    df-bits
    @9
    vm
    cn0
    nn0ex
    rabex
    fvmpt
end
