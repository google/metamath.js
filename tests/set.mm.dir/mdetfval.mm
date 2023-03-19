include "cmdat.mm"
include "co.mm"
include "cv.mm"
include "ccom.mm"
include "cfv.mm"
include "cmpt.mm"
include "cgsu.mm"
include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "wceq.mm"
include "cmat.mm"
include "cbs.mm"
include "csymg.mm"
include "czrh.mm"
include "cpsgn.mm"
include "cmgp.mm"
include "cmulr.mm"
include "oveq12.mm"
include "syl6eqr.mm"
include "fveq2d.mm"
include "simpr.mm"
include "simpl.mm"
include "fveq2.mm"
include "adantl.mm"
include "adantr.mm"
include "coeq12d.mm"
include "fveq1d.mm"
include "mpteq1d.mm"
include "oveq12d.mm"
include "oveq123d.mm"
include "mpteq12dv.mm"
include "df-mdet.mm"
include "fvex.mm"
include "eqeltri.mm"
include "mptex.mm"
include "ovmpt2a.mm"
include "wn.mm"
include "c0.mm"
include "reldmmpt2.mm"
include "ovprc.mm"
include "mpt0.mm"
include "cfn.mm"
include "cxp.mm"
include "cfrlm.mm"
include "cnx.mm"
include "cotp.mm"
include "cmmul.mm"
include "cop.mm"
include "csts.mm"
include "df-mat.mm"
include "syl5eq.mm"
include "base0.mm"
include "3eqtr4g.mm"
include "eqtr4d.mm"
include "pm2.61i.mm"
include "eqtri.mm"

theorem mdetfval
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cD: class D
  let cP: class P
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let cU: class U
  let vm: setvar m
  let cN: class N
  let cY: class Y
  let vp: setvar p
  let vy: setvar y
  let vz: setvar z
  let vn: setvar n
  let vr: setvar r
  let cM: class M
  assume mdetfval.d: |- D = ( N maDet R )
  assume mdetfval.a: |- A = ( N Mat R )
  assume mdetfval.b: |- B = ( Base ` A )
  assume mdetfval.p: |- P = ( Base ` ( SymGrp ` N ) )
  assume mdetfval.y: |- Y = ( ZRHom ` R )
  assume mdetfval.s: |- S = ( pmSgn ` N )
  assume mdetfval.t: |- .x. = ( .r ` R )
  assume mdetfval.u: |- U = ( mulGrp ` R )

  disjoint B m
  disjoint m p
  disjoint m x
  disjoint p x
  disjoint N m
  disjoint N p
  disjoint N x
  disjoint P m
  disjoint R m
  disjoint R p
  disjoint R x
  disjoint S m
  disjoint .x. m
  disjoint U m
  disjoint Y m
  disjoint y z
  disjoint m n
  disjoint m r
  disjoint n r
  disjoint B n
  disjoint B r
  disjoint M m
  disjoint M p
  disjoint M x
  disjoint n p
  disjoint n x
  disjoint N n
  disjoint p r
  disjoint r x
  disjoint N r
  disjoint P n
  disjoint P r
  disjoint R n
  disjoint R r
  disjoint S n
  disjoint S r
  disjoint .x. n
  disjoint .x. r
  disjoint U n
  disjoint U r
  disjoint Y n
  disjoint Y r
  assert |- D = ( m e. B |-> ( R gsum ( p e. P |-> ( ( ( Y o. S ) ` p ) .x. ( U gsum ( x e. N |-> ( ( p ` x ) m x ) ) ) ) ) ) )

  proof
    cD
    cN
    cR
    cmdat
    co
    #
    vm
    cB
    cR
    vp
    cP
    vp
    cv
    #
    cY
    cS
    ccom
    #
    cfv
    #
    cU
    vx
    cN
    vx
    cv
    #
    @1
    cfv
    @4
    vm
    cv
    co
    #
    cmpt
    #
    cgsu
    co
    #
    c.x
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cmpt
    #
    mdetfval.d
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
    @14
    vp
    @13
    csymg
    cfv
    #
    cbs
    cfv
    #
    @1
    @14
    czrh
    cfv
    #
    @13
    cpsgn
    cfv
    #
    ccom
    #
    cfv
    #
    @14
    cmgp
    cfv
    #
    vx
    @13
    @5
    cmpt
    #
    cgsu
    co
    #
    @14
    cmulr
    cfv
    #
    co
    #
    cmpt
    #
    cgsu
    co
    #
    cmpt
    #
    @11
    cmdat
    @13
    cN
    wceq
    #
    @14
    cR
    wceq
    #
    wa
    #
    vm
    @16
    @29
    cB
    @10
    @33
    @16
    cA
    cbs
    cfv
    #
    cB
    @33
    @15
    cA
    cbs
    @33
    @15
    cN
    cR
    cmat
    co
    #
    cA
    @13
    cN
    @14
    cR
    cmat
    oveq12
    mdetfval.a
    syl6eqr
    fveq2d
    mdetfval.b
    syl6eqr
    @33
    @14
    cR
    @28
    @9
    cgsu
    @31
    @32
    simpr
    #
    @33
    vp
    @18
    @27
    cP
    @8
    @33
    @18
    cN
    csymg
    cfv
    #
    cbs
    cfv
    cP
    @33
    @17
    @37
    cbs
    @33
    @13
    cN
    csymg
    @31
    @32
    simpl
    #
    fveq2d
    fveq2d
    mdetfval.p
    syl6eqr
    @33
    @22
    @3
    @25
    @7
    @26
    c.x
    @33
    @26
    cR
    cmulr
    cfv
    #
    c.x
    @32
    @26
    @39
    wceq
    @31
    @14
    cR
    cmulr
    fveq2
    adantl
    mdetfval.t
    syl6eqr
    @33
    @1
    @21
    @2
    @33
    @19
    cY
    @20
    cS
    @33
    @19
    cR
    czrh
    cfv
    cY
    @33
    @14
    cR
    czrh
    @36
    fveq2d
    mdetfval.y
    syl6eqr
    @33
    @20
    cN
    cpsgn
    cfv
    #
    cS
    @31
    @20
    @40
    wceq
    @32
    @13
    cN
    cpsgn
    fveq2
    adantr
    mdetfval.s
    syl6eqr
    coeq12d
    fveq1d
    @33
    @23
    cU
    @24
    @6
    cgsu
    @33
    @23
    cR
    cmgp
    cfv
    #
    cU
    @32
    @23
    @41
    wceq
    @31
    @14
    cR
    cmgp
    fveq2
    adantl
    mdetfval.u
    syl6eqr
    @33
    vx
    @13
    cN
    @5
    @38
    mpteq1d
    oveq12d
    oveq123d
    mpteq12dv
    oveq12d
    mpteq12dv
    vx
    vm
    vn
    vr
    vp
    df-mdet
    #
    vm
    cB
    @10
    cB
    @34
    cvv
    mdetfval.b
    cA
    cbs
    fvex
    eqeltri
    mptex
    ovmpt2a
    @12
    wn
    #
    @0
    vm
    c0
    @10
    cmpt
    #
    @11
    @43
    @0
    c0
    @44
    cN
    cR
    cmdat
    vn
    vr
    cvv
    cvv
    @30
    cmdat
    @42
    reldmmpt2
    ovprc
    vm
    @10
    mpt0
    syl6eqr
    @43
    vm
    cB
    c0
    @10
    @43
    @34
    c0
    cbs
    cfv
    cB
    c0
    @43
    cA
    c0
    cbs
    @43
    cA
    @35
    c0
    mdetfval.a
    cN
    cR
    cmat
    vy
    vz
    cfn
    cvv
    vz
    cv
    #
    vy
    cv
    #
    @46
    cxp
    cfrlm
    co
    cnx
    cmulr
    cfv
    @45
    @46
    @46
    @46
    cotp
    cmmul
    co
    cop
    csts
    co
    cmat
    vy
    vz
    df-mat
    reldmmpt2
    ovprc
    syl5eq
    fveq2d
    mdetfval.b
    base0
    3eqtr4g
    mpteq1d
    eqtr4d
    pm2.61i
    eqtri
end
