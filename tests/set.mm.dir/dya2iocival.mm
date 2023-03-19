include "cz.mm"
include "wcel.mm"
include "co.mm"
include "c2.mm"
include "cexp.mm"
include "cdiv.mm"
include "c1.mm"
include "caddc.mm"
include "cico.mm"
include "wceq.mm"
include "cv.mm"
include "oveq1.mm"
include "oveq1d.mm"
include "oveq12d.mm"
include "oveq2.mm"
include "oveq2d.mm"
include "cmpt2.mm"
include "cbvmpt2v.mm"
include "eqtr4i.mm"
include "ovex.mm"
include "ovmpt2.mm"
include "ancoms.mm"

theorem dya2iocival
  let vx: setvar x
  let vn: setvar n
  let cI: class I
  let cJ: class J
  let cN: class N
  let cX: class X
  let vm: setvar m
  let vu: setvar u
  assume sxbrsiga.0: |- J = ( topGen ` ran (,) )
  assume dya2ioc.1: |- I = ( x e. ZZ , n e. ZZ |-> ( ( x / ( 2 ^ n ) ) [,) ( ( x + 1 ) / ( 2 ^ n ) ) ) )

  disjoint n x
  disjoint n x
  disjoint m n
  disjoint m u
  disjoint m x
  disjoint n u
  disjoint u x
  disjoint N m
  disjoint N u
  disjoint X m
  disjoint X u
  assert |- ( ( N e. ZZ /\ X e. ZZ ) -> ( X I N ) = ( ( X / ( 2 ^ N ) ) [,) ( ( X + 1 ) / ( 2 ^ N ) ) ) )

  proof
    cX
    cz
    wcel
    cN
    cz
    wcel
    cX
    cN
    cI
    co
    cX
    c2
    cN
    cexp
    co
    #
    cdiv
    co
    #
    cX
    c1
    caddc
    co
    #
    @0
    cdiv
    co
    #
    cico
    co
    #
    wceq
    vu
    vm
    cX
    cN
    cz
    cz
    vu
    cv
    #
    c2
    vm
    cv
    #
    cexp
    co
    #
    cdiv
    co
    #
    @5
    c1
    caddc
    co
    #
    @7
    cdiv
    co
    #
    cico
    co
    #
    @4
    cI
    cX
    @7
    cdiv
    co
    #
    @2
    @7
    cdiv
    co
    #
    cico
    co
    @5
    cX
    wceq
    #
    @8
    @12
    @10
    @13
    cico
    @5
    cX
    @7
    cdiv
    oveq1
    @14
    @9
    @2
    @7
    cdiv
    @5
    cX
    c1
    caddc
    oveq1
    oveq1d
    oveq12d
    @6
    cN
    wceq
    #
    @12
    @1
    @13
    @3
    cico
    @15
    @7
    @0
    cX
    cdiv
    @6
    cN
    c2
    cexp
    oveq2
    #
    oveq2d
    @15
    @7
    @0
    @2
    cdiv
    @16
    oveq2d
    oveq12d
    cI
    vx
    vn
    cz
    cz
    vx
    cv
    #
    c2
    vn
    cv
    #
    cexp
    co
    #
    cdiv
    co
    #
    @17
    c1
    caddc
    co
    #
    @19
    cdiv
    co
    #
    cico
    co
    #
    cmpt2
    vu
    vm
    cz
    cz
    @11
    cmpt2
    dya2ioc.1
    vu
    vm
    vx
    vn
    cz
    cz
    @11
    @23
    @17
    @7
    cdiv
    co
    #
    @21
    @7
    cdiv
    co
    #
    cico
    co
    @5
    @17
    wceq
    #
    @8
    @24
    @10
    @25
    cico
    @5
    @17
    @7
    cdiv
    oveq1
    @26
    @9
    @21
    @7
    cdiv
    @5
    @17
    c1
    caddc
    oveq1
    oveq1d
    oveq12d
    @6
    @18
    wceq
    #
    @24
    @20
    @25
    @22
    cico
    @27
    @7
    @19
    @17
    cdiv
    @6
    @18
    c2
    cexp
    oveq2
    #
    oveq2d
    @27
    @7
    @19
    @21
    cdiv
    @28
    oveq2d
    oveq12d
    cbvmpt2v
    eqtr4i
    @1
    @3
    cico
    ovex
    ovmpt2
    ancoms
end
