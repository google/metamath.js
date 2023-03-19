include "cfuc.mm"
include "co.mm"
include "cnx.mm"
include "cbs.mm"
include "cfv.mm"
include "cop.mm"
include "chom.mm"
include "cco.mm"
include "ctp.mm"
include "ccat.mm"
include "cv.mm"
include "cfunc.mm"
include "cnat.mm"
include "cxp.mm"
include "c1st.mm"
include "c2nd.mm"
include "cmpt.mm"
include "cmpt2.mm"
include "csb.mm"
include "cvv.mm"
include "wceq.mm"
include "df-fuc.mm"
include "a1i.mm"
include "wa.mm"
include "simprl.mm"
include "simprr.mm"
include "oveq12d.mm"
include "syl6eqr.mm"
include "opeq2d.mm"
include "sqxpeqd.mm"
include "oveqd.mm"
include "fveq2d.mm"
include "mpteq12dv.mm"
include "mpt2eq123dv.mm"
include "csbeq2dv.mm"
include "adantr.mm"
include "eqtr4d.mm"
include "tpeq123d.mm"
include "wcel.mm"
include "tpex.mm"
include "ovmpt2d.mm"
include "syl5eq.mm"

theorem fucval
  let wph: wff ph
  let vx: setvar x
  let vv: setvar v
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cQ: class Q
  let c.xb: class .xb
  let c.x: class .x.
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let cN: class N
  let va: setvar a
  let vb: setvar b
  let vt: setvar t
  let vu: setvar u
  assume fucval.q: |- Q = ( C FuncCat D )
  assume fucval.b: |- B = ( C Func D )
  assume fucval.n: |- N = ( C Nat D )
  assume fucval.a: |- A = ( Base ` C )
  assume fucval.o: |- .x. = ( comp ` D )
  assume fucval.c: |- ( ph -> C e. Cat )
  assume fucval.d: |- ( ph -> D e. Cat )
  assume fucval.x: |- ( ph -> .xb = ( v e. ( B X. B ) , h e. B |-> [_ ( 1st ` v ) / f ]_ [_ ( 2nd ` v ) / g ]_ ( b e. ( g N h ) , a e. ( f N g ) |-> ( x e. A |-> ( ( b ` x ) ( <. ( ( 1st ` f ) ` x ) , ( ( 1st ` g ) ` x ) >. .x. ( ( 1st ` h ) ` x ) ) ( a ` x ) ) ) ) ) )

  disjoint h v
  disjoint B h
  disjoint B v
  disjoint a b
  disjoint a f
  disjoint a g
  disjoint a h
  disjoint a v
  disjoint a x
  disjoint a ph
  disjoint b f
  disjoint b g
  disjoint b h
  disjoint b v
  disjoint b x
  disjoint b ph
  disjoint f g
  disjoint f h
  disjoint f v
  disjoint f x
  disjoint f ph
  disjoint g h
  disjoint g v
  disjoint g x
  disjoint g ph
  disjoint h x
  disjoint h ph
  disjoint v x
  disjoint ph v
  disjoint ph x
  disjoint C a
  disjoint C b
  disjoint C f
  disjoint C g
  disjoint C h
  disjoint C v
  disjoint C x
  disjoint D a
  disjoint D b
  disjoint D f
  disjoint D g
  disjoint D h
  disjoint D v
  disjoint D x
  disjoint h t
  disjoint h u
  disjoint t u
  disjoint t v
  disjoint B t
  disjoint u v
  disjoint B u
  disjoint N t
  disjoint N u
  disjoint a t
  disjoint a u
  disjoint b t
  disjoint b u
  disjoint f t
  disjoint f u
  disjoint g t
  disjoint g u
  disjoint t x
  disjoint ph t
  disjoint u x
  disjoint ph u
  disjoint .xb t
  disjoint .xb u
  disjoint C t
  disjoint C u
  disjoint D t
  disjoint D u
  assert |- ( ph -> Q = { <. ( Base ` ndx ) , B >. , <. ( Hom ` ndx ) , N >. , <. ( comp ` ndx ) , .xb >. } )

  proof
    wph
    cQ
    cC
    cD
    cfuc
    co
    cnx
    cbs
    cfv
    #
    cB
    cop
    #
    cnx
    chom
    cfv
    #
    cN
    cop
    #
    cnx
    cco
    cfv
    #
    c.xb
    cop
    #
    ctp
    #
    fucval.q
    wph
    vt
    vu
    cC
    cD
    ccat
    ccat
    @0
    vt
    cv
    #
    vu
    cv
    #
    cfunc
    co
    #
    cop
    #
    @2
    @7
    @8
    cnat
    co
    #
    cop
    #
    @4
    vv
    vh
    @9
    @9
    cxp
    #
    @9
    vf
    vv
    cv
    #
    c1st
    cfv
    #
    vg
    @14
    c2nd
    cfv
    #
    vb
    va
    vg
    cv
    #
    vh
    cv
    #
    @11
    co
    #
    vf
    cv
    #
    @17
    @11
    co
    #
    vx
    @7
    cbs
    cfv
    #
    vx
    cv
    #
    vb
    cv
    cfv
    #
    @23
    va
    cv
    cfv
    #
    @23
    @20
    c1st
    cfv
    cfv
    @23
    @17
    c1st
    cfv
    cfv
    cop
    #
    @23
    @18
    c1st
    cfv
    cfv
    #
    @8
    cco
    cfv
    #
    co
    #
    co
    #
    cmpt
    #
    cmpt2
    #
    csb
    #
    csb
    #
    cmpt2
    #
    cop
    #
    ctp
    #
    @6
    cfuc
    cvv
    cfuc
    vt
    vu
    ccat
    ccat
    @37
    cmpt2
    wceq
    wph
    vx
    vv
    vu
    vt
    vf
    vg
    vh
    va
    vb
    df-fuc
    a1i
    wph
    @7
    cC
    wceq
    #
    @8
    cD
    wceq
    #
    wa
    #
    wa
    #
    @10
    @1
    @12
    @3
    @36
    @5
    @41
    @9
    cB
    @0
    @41
    @9
    cC
    cD
    cfunc
    co
    cB
    @41
    @7
    cC
    @8
    cD
    cfunc
    wph
    @38
    @39
    simprl
    #
    wph
    @38
    @39
    simprr
    #
    oveq12d
    fucval.b
    syl6eqr
    #
    opeq2d
    @41
    @11
    cN
    @2
    @41
    @11
    cC
    cD
    cnat
    co
    cN
    @41
    @7
    cC
    @8
    cD
    cnat
    @42
    @43
    oveq12d
    fucval.n
    syl6eqr
    #
    opeq2d
    @41
    @35
    c.xb
    @4
    @41
    @35
    vv
    vh
    cB
    cB
    cxp
    #
    cB
    vf
    @15
    vg
    @16
    vb
    va
    @17
    @18
    cN
    co
    #
    @20
    @17
    cN
    co
    #
    vx
    cA
    @24
    @25
    @26
    @27
    c.x
    co
    #
    co
    #
    cmpt
    #
    cmpt2
    #
    csb
    #
    csb
    #
    cmpt2
    #
    c.xb
    @41
    vv
    vh
    @13
    @9
    @34
    @46
    cB
    @54
    @41
    @9
    cB
    @44
    sqxpeqd
    @44
    @41
    vf
    @15
    @33
    @53
    @41
    vg
    @16
    @32
    @52
    @41
    vb
    va
    @19
    @21
    @31
    @47
    @48
    @51
    @41
    @11
    cN
    @17
    @18
    @45
    oveqd
    @41
    @11
    cN
    @20
    @17
    @45
    oveqd
    @41
    vx
    @22
    @30
    cA
    @50
    @41
    @22
    cC
    cbs
    cfv
    cA
    @41
    @7
    cC
    cbs
    @42
    fveq2d
    fucval.a
    syl6eqr
    @41
    @29
    @49
    @24
    @25
    @41
    @28
    c.x
    @26
    @27
    @41
    @28
    cD
    cco
    cfv
    c.x
    @41
    @8
    cD
    cco
    @43
    fveq2d
    fucval.o
    syl6eqr
    oveqd
    oveqd
    mpteq12dv
    mpt2eq123dv
    csbeq2dv
    csbeq2dv
    mpt2eq123dv
    wph
    c.xb
    @55
    wceq
    @40
    fucval.x
    adantr
    eqtr4d
    opeq2d
    tpeq123d
    fucval.c
    fucval.d
    @6
    cvv
    wcel
    wph
    @1
    @3
    @5
    tpex
    a1i
    ovmpt2d
    syl5eq
end
