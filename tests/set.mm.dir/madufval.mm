include "cmadu.mm"
include "co.mm"
include "weq.mm"
include "cif.mm"
include "cv.mm"
include "cmpt2.mm"
include "cfv.mm"
include "cmpt.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "cmat.mm"
include "cbs.mm"
include "cur.mm"
include "c0g.mm"
include "cmdat.mm"
include "oveq1.mm"
include "fveq2d.mm"
include "id.mm"
include "eqidd.mm"
include "mpt2eq123dv.mm"
include "fveq12d.mm"
include "mpteq12dv.mm"
include "oveq2.mm"
include "fveq2.mm"
include "ifeq12d.mm"
include "ifeq1d.mm"
include "mpt2eq3dv.mm"
include "df-madu.mm"
include "fvex.mm"
include "mptex.mm"
include "ovmpt2.mm"
include "fveq2i.mm"
include "eqtri.mm"
include "a1i.mm"
include "mpt2eq3ia.mm"
include "fveq12i.mm"
include "mpteq12i.mm"
include "syl6eqr.mm"
include "wn.mm"
include "c0.mm"
include "reldmmpt2.mm"
include "ovprc.mm"
include "cfn.mm"
include "cxp.mm"
include "cfrlm.mm"
include "cnx.mm"
include "cmulr.mm"
include "cotp.mm"
include "cmmul.mm"
include "cop.mm"
include "csts.mm"
include "df-mat.mm"
include "syl5eq.mm"
include "base0.mm"
include "3eqtr4g.mm"
include "mpteq1d.mm"
include "mpt0.mm"
include "syl6eq.mm"
include "eqtr4d.mm"
include "pm2.61i.mm"

theorem madufval
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let c.1: class .1.
  let vi: setvar i
  let vj: setvar j
  let vk: setvar k
  let vm: setvar m
  let cJ: class J
  let cN: class N
  let c.0: class .0.
  let vl: setvar l
  let vn: setvar n
  let vr: setvar r
  assume madufval.a: |- A = ( N Mat R )
  assume madufval.d: |- D = ( N maDet R )
  assume madufval.j: |- J = ( N maAdju R )
  assume madufval.b: |- B = ( Base ` A )
  assume madufval.o: |- .1. = ( 1r ` R )
  assume madufval.z: |- .0. = ( 0g ` R )

  disjoint N m
  disjoint N i
  disjoint N j
  disjoint N k
  disjoint N l
  disjoint i m
  disjoint j m
  disjoint k m
  disjoint l m
  disjoint i j
  disjoint i k
  disjoint i l
  disjoint j k
  disjoint j l
  disjoint k l
  disjoint R m
  disjoint R i
  disjoint R j
  disjoint R k
  disjoint R l
  disjoint B m
  disjoint N n
  disjoint N r
  disjoint n r
  disjoint m n
  disjoint i n
  disjoint j n
  disjoint k n
  disjoint l n
  disjoint m r
  disjoint i r
  disjoint j r
  disjoint k r
  disjoint l r
  disjoint R n
  disjoint R r
  assert |- J = ( m e. B |-> ( i e. N , j e. N |-> ( D ` ( k e. N , l e. N |-> if ( k = j , if ( l = i , .1. , .0. ) , ( k m l ) ) ) ) ) )

  proof
    cJ
    cN
    cR
    cmadu
    co
    #
    vm
    cB
    vi
    vj
    cN
    cN
    vk
    vl
    cN
    cN
    vk
    vj
    weq
    #
    vl
    vi
    weq
    #
    c.1
    c.0
    cif
    #
    vk
    cv
    #
    vl
    cv
    #
    vm
    cv
    co
    #
    cif
    #
    cmpt2
    #
    cD
    cfv
    #
    cmpt2
    #
    cmpt
    #
    madufval.j
    cN
    cvv
    wcel
    cR
    cvv
    wcel
    wa
    #
    @0
    @11
    wceq
    @12
    @0
    vm
    cN
    cR
    cmat
    co
    #
    cbs
    cfv
    #
    vi
    vj
    cN
    cN
    vk
    vl
    cN
    cN
    @1
    @2
    cR
    cur
    cfv
    #
    cR
    c0g
    cfv
    #
    cif
    #
    @6
    cif
    #
    cmpt2
    #
    cN
    cR
    cmdat
    co
    #
    cfv
    #
    cmpt2
    #
    cmpt
    #
    @11
    vn
    vr
    cN
    cR
    cvv
    cvv
    vm
    vn
    cv
    #
    vr
    cv
    #
    cmat
    co
    #
    cbs
    cfv
    #
    vi
    vj
    @24
    @24
    vk
    vl
    @24
    @24
    @1
    @2
    @25
    cur
    cfv
    #
    @25
    c0g
    cfv
    #
    cif
    #
    @6
    cif
    #
    cmpt2
    #
    @24
    @25
    cmdat
    co
    #
    cfv
    #
    cmpt2
    #
    cmpt
    #
    @23
    cmadu
    vm
    cN
    @25
    cmat
    co
    #
    cbs
    cfv
    #
    vi
    vj
    cN
    cN
    vk
    vl
    cN
    cN
    @31
    cmpt2
    #
    cN
    @25
    cmdat
    co
    #
    cfv
    #
    cmpt2
    #
    cmpt
    @24
    cN
    wceq
    #
    vm
    @27
    @35
    @38
    @42
    @43
    @26
    @37
    cbs
    @24
    cN
    @25
    cmat
    oveq1
    fveq2d
    @43
    vi
    vj
    @24
    @24
    @34
    cN
    cN
    @41
    @43
    id
    #
    @44
    @43
    @32
    @39
    @33
    @40
    @24
    cN
    @25
    cmdat
    oveq1
    @43
    vk
    vl
    @24
    @24
    @31
    cN
    cN
    @31
    @44
    @44
    @43
    @31
    eqidd
    mpt2eq123dv
    fveq12d
    mpt2eq123dv
    mpteq12dv
    @25
    cR
    wceq
    #
    vm
    @38
    @42
    @14
    @22
    @45
    @37
    @13
    cbs
    @25
    cR
    cN
    cmat
    oveq2
    fveq2d
    @45
    vi
    vj
    cN
    cN
    @41
    @21
    @45
    @39
    @19
    @40
    @20
    @25
    cR
    cN
    cmdat
    oveq2
    @45
    vk
    vl
    cN
    cN
    @31
    @18
    @45
    @1
    @30
    @17
    @6
    @45
    @2
    @28
    @15
    @29
    @16
    @25
    cR
    cur
    fveq2
    @25
    cR
    c0g
    fveq2
    ifeq12d
    ifeq1d
    mpt2eq3dv
    fveq12d
    mpt2eq3dv
    mpteq12dv
    vi
    vj
    vk
    vm
    vn
    vr
    vl
    df-madu
    #
    vm
    @14
    @22
    @13
    cbs
    fvex
    mptex
    ovmpt2
    vm
    cB
    @10
    @14
    @22
    cB
    cA
    cbs
    cfv
    #
    @14
    madufval.b
    cA
    @13
    cbs
    madufval.a
    fveq2i
    eqtri
    vi
    vj
    cN
    cN
    @9
    @21
    @9
    @21
    wceq
    vi
    cv
    cN
    wcel
    vj
    cv
    cN
    wcel
    wa
    @8
    @19
    cD
    @20
    madufval.d
    vk
    vl
    cN
    cN
    @7
    @18
    @4
    cN
    wcel
    @5
    cN
    wcel
    wa
    #
    @1
    @3
    @17
    @6
    @48
    @2
    c.1
    @15
    c.0
    @16
    c.1
    @15
    wceq
    @48
    madufval.o
    a1i
    c.0
    @16
    wceq
    @48
    madufval.z
    a1i
    ifeq12d
    ifeq1d
    mpt2eq3ia
    fveq12i
    a1i
    mpt2eq3ia
    mpteq12i
    syl6eqr
    @12
    wn
    #
    @0
    c0
    @11
    cN
    cR
    cmadu
    vn
    vr
    cvv
    cvv
    @36
    cmadu
    @46
    reldmmpt2
    ovprc
    @49
    @11
    vm
    c0
    @10
    cmpt
    c0
    @49
    vm
    cB
    c0
    @10
    @49
    @47
    c0
    cbs
    cfv
    cB
    c0
    @49
    cA
    c0
    cbs
    @49
    cA
    @13
    c0
    madufval.a
    cN
    cR
    cmat
    vn
    vr
    cfn
    cvv
    @25
    @24
    @24
    cxp
    cfrlm
    co
    cnx
    cmulr
    cfv
    @25
    @24
    @24
    @24
    cotp
    cmmul
    co
    cop
    csts
    co
    cmat
    vn
    vr
    df-mat
    reldmmpt2
    ovprc
    syl5eq
    fveq2d
    madufval.b
    base0
    3eqtr4g
    mpteq1d
    vm
    @10
    mpt0
    syl6eq
    eqtr4d
    pm2.61i
    eqtri
end
