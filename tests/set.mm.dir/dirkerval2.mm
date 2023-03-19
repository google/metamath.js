include "cn.mm"
include "wcel.mm"
include "cr.mm"
include "wa.mm"
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
include "dirkerval.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "oveq2.mm"
include "fveq2d.mm"
include "oveq2d.mm"
include "oveq12d.mm"
include "ifbieq2d.mm"
include "cbvmptv.mm"
include "syl6eq.mm"
include "adantr.mm"
include "simpr.mm"
include "oveq1d.mm"
include "2re.mm"
include "a1i.mm"
include "nnre.mm"
include "remulcld.mm"
include "1red.mm"
include "readdcld.mm"
include "pire.mm"
include "2cnd.mm"
include "recnd.mm"
include "clt.mm"
include "wbr.mm"
include "2pos.mm"
include "gt0ne0d.mm"
include "pipos.mm"
include "mulne0d.mm"
include "redivcld.mm"
include "ad2antrr.mm"
include "dirker2re.mm"
include "ifclda.mm"
include "fvmptd.mm"

theorem dirkerval2
  let cD: class D
  let cS: class S
  let vn: setvar n
  let cN: class N
  let vs: setvar s
  let vt: setvar t
  let vk: setvar k
  let vx: setvar x
  assume dirkerval2.1: |- D = ( n e. NN |-> ( s e. RR |-> if ( ( s mod ( 2 x. _pi ) ) = 0 , ( ( ( 2 x. n ) + 1 ) / ( 2 x. _pi ) ) , ( ( sin ` ( ( n + ( 1 / 2 ) ) x. s ) ) / ( ( 2 x. _pi ) x. ( sin ` ( s / 2 ) ) ) ) ) ) )

  disjoint N s
  disjoint n s
  disjoint N t
  disjoint s t
  disjoint S t
  disjoint k x
  assert |- ( ( N e. NN /\ S e. RR ) -> ( ( D ` N ) ` S ) = if ( ( S mod ( 2 x. _pi ) ) = 0 , ( ( ( 2 x. N ) + 1 ) / ( 2 x. _pi ) ) , ( ( sin ` ( ( N + ( 1 / 2 ) ) x. S ) ) / ( ( 2 x. _pi ) x. ( sin ` ( S / 2 ) ) ) ) ) )

  proof
    cN
    cn
    wcel
    #
    cS
    cr
    wcel
    #
    wa
    #
    vt
    cS
    vt
    cv
    #
    c2
    cpi
    cmul
    co
    #
    cmo
    co
    #
    cc0
    wceq
    #
    c2
    cN
    cmul
    co
    #
    c1
    caddc
    co
    #
    @4
    cdiv
    co
    #
    cN
    c1
    c2
    cdiv
    co
    caddc
    co
    #
    @3
    cmul
    co
    #
    csin
    cfv
    #
    @4
    @3
    c2
    cdiv
    co
    #
    csin
    cfv
    #
    cmul
    co
    #
    cdiv
    co
    #
    cif
    #
    cS
    @4
    cmo
    co
    #
    cc0
    wceq
    #
    @9
    @10
    cS
    cmul
    co
    #
    csin
    cfv
    #
    @4
    cS
    c2
    cdiv
    co
    #
    csin
    cfv
    #
    cmul
    co
    #
    cdiv
    co
    #
    cif
    cr
    cN
    cD
    cfv
    #
    cr
    @0
    @26
    vt
    cr
    @17
    cmpt
    #
    wceq
    @1
    @0
    @26
    vs
    cr
    vs
    cv
    #
    @4
    cmo
    co
    #
    cc0
    wceq
    #
    @9
    @10
    @28
    cmul
    co
    #
    csin
    cfv
    #
    @4
    @28
    c2
    cdiv
    co
    #
    csin
    cfv
    #
    cmul
    co
    #
    cdiv
    co
    #
    cif
    #
    cmpt
    @27
    cD
    vn
    cN
    vs
    dirkerval2.1
    dirkerval
    vs
    vt
    cr
    @37
    @17
    @28
    @3
    wceq
    #
    @30
    @6
    @36
    @16
    @9
    @38
    @29
    @5
    cc0
    @28
    @3
    @4
    cmo
    oveq1
    eqeq1d
    @38
    @32
    @12
    @35
    @15
    cdiv
    @38
    @31
    @11
    csin
    @28
    @3
    @10
    cmul
    oveq2
    fveq2d
    @38
    @34
    @14
    @4
    cmul
    @38
    @33
    @13
    csin
    @28
    @3
    c2
    cdiv
    oveq1
    fveq2d
    oveq2d
    oveq12d
    ifbieq2d
    cbvmptv
    syl6eq
    adantr
    @2
    @3
    cS
    wceq
    #
    wa
    #
    @6
    @19
    @16
    @25
    @9
    @40
    @5
    @18
    cc0
    @40
    @3
    cS
    @4
    cmo
    @2
    @39
    simpr
    #
    oveq1d
    eqeq1d
    @40
    @12
    @21
    @15
    @24
    cdiv
    @40
    @11
    @20
    csin
    @40
    @3
    cS
    @10
    cmul
    @41
    oveq2d
    fveq2d
    @40
    @14
    @23
    @4
    cmul
    @40
    @13
    @22
    csin
    @40
    @3
    cS
    c2
    cdiv
    @41
    oveq1d
    fveq2d
    oveq2d
    oveq12d
    ifbieq2d
    @0
    @1
    simpr
    @2
    @19
    @9
    @25
    cr
    @0
    @9
    cr
    wcel
    @1
    @19
    @0
    @8
    @4
    @0
    @7
    c1
    @0
    c2
    cN
    c2
    cr
    wcel
    @0
    2re
    a1i
    #
    cN
    nnre
    remulcld
    @0
    1red
    readdcld
    @0
    c2
    cpi
    @42
    cpi
    cr
    wcel
    @0
    pire
    a1i
    #
    remulcld
    @0
    c2
    cpi
    @0
    2cnd
    @0
    cpi
    @43
    recnd
    @0
    c2
    cc0
    c2
    clt
    wbr
    @0
    2pos
    a1i
    gt0ne0d
    @0
    cpi
    cc0
    cpi
    clt
    wbr
    @0
    pipos
    a1i
    gt0ne0d
    mulne0d
    redivcld
    ad2antrr
    cS
    cN
    dirker2re
    ifclda
    fvmptd
end
