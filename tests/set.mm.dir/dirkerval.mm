include "cr.mm"
include "cv.mm"
include "c2.mm"
include "cpi.mm"
include "cmul.mm"
include "co.mm"
include "cmo.mm"
include "cc0.mm"
include "wceq.mm"
include "c1.mm"
include "caddc.mm"
include "cdiv.mm"
include "csin.mm"
include "cfv.mm"
include "cif.mm"
include "cmpt.mm"
include "cn.mm"
include "wcel.mm"
include "wa.mm"
include "simpl.mm"
include "oveq2d.mm"
include "oveq1d.mm"
include "fveq2d.mm"
include "ifeq12d.mm"
include "mpteq2dva.mm"
include "cbvmptv.mm"
include "eqtri.mm"
include "reex.mm"
include "mptex.mm"
include "fvmpt.mm"

theorem dirkerval
  let cD: class D
  let vn: setvar n
  let cN: class N
  let vs: setvar s
  let vm: setvar m
  let vk: setvar k
  let vx: setvar x
  assume dirkerval.1: |- D = ( n e. NN |-> ( s e. RR |-> if ( ( s mod ( 2 x. _pi ) ) = 0 , ( ( ( 2 x. n ) + 1 ) / ( 2 x. _pi ) ) , ( ( sin ` ( ( n + ( 1 / 2 ) ) x. s ) ) / ( ( 2 x. _pi ) x. ( sin ` ( s / 2 ) ) ) ) ) ) )

  disjoint N s
  disjoint n s
  disjoint N m
  disjoint m s
  disjoint m n
  disjoint k x
  assert |- ( N e. NN -> ( D ` N ) = ( s e. RR |-> if ( ( s mod ( 2 x. _pi ) ) = 0 , ( ( ( 2 x. N ) + 1 ) / ( 2 x. _pi ) ) , ( ( sin ` ( ( N + ( 1 / 2 ) ) x. s ) ) / ( ( 2 x. _pi ) x. ( sin ` ( s / 2 ) ) ) ) ) ) )

  proof
    vm
    cN
    vs
    cr
    vs
    cv
    #
    c2
    cpi
    cmul
    co
    #
    cmo
    co
    cc0
    wceq
    #
    c2
    vm
    cv
    #
    cmul
    co
    #
    c1
    caddc
    co
    #
    @1
    cdiv
    co
    #
    @3
    c1
    c2
    cdiv
    co
    #
    caddc
    co
    #
    @0
    cmul
    co
    #
    csin
    cfv
    #
    @1
    @0
    c2
    cdiv
    co
    csin
    cfv
    cmul
    co
    #
    cdiv
    co
    #
    cif
    #
    cmpt
    #
    vs
    cr
    @2
    c2
    cN
    cmul
    co
    #
    c1
    caddc
    co
    #
    @1
    cdiv
    co
    #
    cN
    @7
    caddc
    co
    #
    @0
    cmul
    co
    #
    csin
    cfv
    #
    @11
    cdiv
    co
    #
    cif
    #
    cmpt
    cn
    cD
    @3
    cN
    wceq
    #
    vs
    cr
    @13
    @22
    @23
    @0
    cr
    wcel
    #
    wa
    #
    @2
    @6
    @17
    @12
    @21
    @25
    @5
    @16
    @1
    cdiv
    @25
    @4
    @15
    c1
    caddc
    @25
    @3
    cN
    c2
    cmul
    @23
    @24
    simpl
    #
    oveq2d
    oveq1d
    oveq1d
    @25
    @10
    @20
    @11
    cdiv
    @25
    @9
    @19
    csin
    @25
    @8
    @18
    @0
    cmul
    @25
    @3
    cN
    @7
    caddc
    @26
    oveq1d
    oveq1d
    fveq2d
    oveq1d
    ifeq12d
    mpteq2dva
    cD
    vn
    cn
    vs
    cr
    @2
    c2
    vn
    cv
    #
    cmul
    co
    #
    c1
    caddc
    co
    #
    @1
    cdiv
    co
    #
    @27
    @7
    caddc
    co
    #
    @0
    cmul
    co
    #
    csin
    cfv
    #
    @11
    cdiv
    co
    #
    cif
    #
    cmpt
    #
    cmpt
    vm
    cn
    @14
    cmpt
    dirkerval.1
    vn
    vm
    cn
    @36
    @14
    @27
    @3
    wceq
    #
    vs
    cr
    @35
    @13
    @37
    @24
    wa
    #
    @2
    @30
    @6
    @34
    @12
    @38
    @29
    @5
    @1
    cdiv
    @38
    @28
    @4
    c1
    caddc
    @38
    @27
    @3
    c2
    cmul
    @37
    @24
    simpl
    #
    oveq2d
    oveq1d
    oveq1d
    @38
    @33
    @10
    @11
    cdiv
    @38
    @32
    @9
    csin
    @38
    @31
    @8
    @0
    cmul
    @38
    @27
    @3
    @7
    caddc
    @39
    oveq1d
    oveq1d
    fveq2d
    oveq1d
    ifeq12d
    mpteq2dva
    cbvmptv
    eqtri
    vs
    cr
    @22
    reex
    mptex
    fvmpt
end
