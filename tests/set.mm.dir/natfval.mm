include "cnat.mm"
include "co.mm"
include "cfunc.mm"
include "cv.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "cop.mm"
include "wceq.mm"
include "wral.mm"
include "cixp.mm"
include "crab.mm"
include "csb.mm"
include "cmpt2.mm"
include "ccat.mm"
include "wcel.mm"
include "wa.mm"
include "cco.mm"
include "chom.mm"
include "cbs.mm"
include "oveq12.mm"
include "simpl.mm"
include "fveq2d.mm"
include "syl6eqr.mm"
include "ixpeq1d.mm"
include "simpr.mm"
include "oveqd.mm"
include "ixpeq2dv.mm"
include "eqtrd.mm"
include "eqeq12d.mm"
include "raleqbidv.mm"
include "rabeqbidv.mm"
include "csbeq2dv.mm"
include "mpt2eq123dv.mm"
include "df-nat.mm"
include "ovex.mm"
include "mpt2ex.mm"
include "ovmpt2a.mm"
include "wn.mm"
include "c0.mm"
include "mpt2ndm0.mm"
include "funcrcl.mm"
include "con3i.mm"
include "eq0rdv.mm"
include "mpt2eq12.mm"
include "syl2anc.mm"
include "mpt20.mm"
include "syl6eq.mm"
include "eqtr4d.mm"
include "pm2.61i.mm"
include "eqtri.mm"

theorem natfval
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cC: class C
  let cD: class D
  let c.x: class .x.
  let vf: setvar f
  let vg: setvar g
  let vh: setvar h
  let cH: class H
  let cJ: class J
  let cN: class N
  let vs: setvar s
  let vr: setvar r
  let va: setvar a
  let vb: setvar b
  let vt: setvar t
  let vu: setvar u
  let vv: setvar v
  let cA: class A
  let cF: class F
  let cG: class G
  let wph: wff ph
  let cK: class K
  let cL: class L
  assume natfval.1: |- N = ( C Nat D )
  assume natfval.b: |- B = ( Base ` C )
  assume natfval.h: |- H = ( Hom ` C )
  assume natfval.j: |- J = ( Hom ` D )
  assume natfval.o: |- .x. = ( comp ` D )

  disjoint a f
  disjoint a g
  disjoint a h
  disjoint a r
  disjoint a s
  disjoint a x
  disjoint a y
  disjoint f g
  disjoint f h
  disjoint f r
  disjoint f s
  disjoint f x
  disjoint f y
  disjoint g h
  disjoint g r
  disjoint g s
  disjoint g x
  disjoint g y
  disjoint h r
  disjoint h s
  disjoint h x
  disjoint h y
  disjoint r s
  disjoint r x
  disjoint r y
  disjoint s x
  disjoint s y
  disjoint x y
  disjoint B a
  disjoint B f
  disjoint B g
  disjoint B r
  disjoint B s
  disjoint B x
  disjoint B y
  disjoint C a
  disjoint C f
  disjoint C g
  disjoint C h
  disjoint C r
  disjoint C s
  disjoint C x
  disjoint C y
  disjoint J a
  disjoint J f
  disjoint J g
  disjoint J r
  disjoint J s
  disjoint H a
  disjoint H f
  disjoint H g
  disjoint H h
  disjoint H r
  disjoint H s
  disjoint .x. a
  disjoint .x. f
  disjoint .x. g
  disjoint .x. r
  disjoint .x. s
  disjoint D a
  disjoint D f
  disjoint D g
  disjoint D h
  disjoint D r
  disjoint D s
  disjoint D x
  disjoint D y
  disjoint a b
  disjoint a t
  disjoint a u
  disjoint a v
  disjoint b f
  disjoint b g
  disjoint b h
  disjoint b r
  disjoint b s
  disjoint b t
  disjoint b u
  disjoint b v
  disjoint b x
  disjoint b y
  disjoint f t
  disjoint f u
  disjoint f v
  disjoint g t
  disjoint g u
  disjoint g v
  disjoint h t
  disjoint h u
  disjoint h v
  disjoint r t
  disjoint r u
  disjoint r v
  disjoint s t
  disjoint s u
  disjoint s v
  disjoint t u
  disjoint t v
  disjoint t x
  disjoint t y
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint v x
  disjoint v y
  disjoint A a
  disjoint A h
  disjoint A x
  disjoint A y
  disjoint B t
  disjoint B u
  disjoint C t
  disjoint C u
  disjoint F a
  disjoint F f
  disjoint F g
  disjoint F h
  disjoint F r
  disjoint F s
  disjoint F x
  disjoint F y
  disjoint J t
  disjoint J u
  disjoint G a
  disjoint G f
  disjoint G g
  disjoint G h
  disjoint G r
  disjoint G s
  disjoint G x
  disjoint G y
  disjoint H t
  disjoint H u
  disjoint a ph
  disjoint f ph
  disjoint g ph
  disjoint h ph
  disjoint ph r
  disjoint ph s
  disjoint ph x
  disjoint ph y
  disjoint K a
  disjoint K f
  disjoint K g
  disjoint K h
  disjoint K r
  disjoint K s
  disjoint K x
  disjoint K y
  disjoint L a
  disjoint L f
  disjoint L g
  disjoint L h
  disjoint L r
  disjoint L s
  disjoint L x
  disjoint L y
  disjoint .x. t
  disjoint .x. u
  disjoint D t
  disjoint D u
  assert |- N = ( f e. ( C Func D ) , g e. ( C Func D ) |-> [_ ( 1st ` f ) / r ]_ [_ ( 1st ` g ) / s ]_ { a e. X_ x e. B ( ( r ` x ) J ( s ` x ) ) | A. x e. B A. y e. B A. h e. ( x H y ) ( ( a ` y ) ( <. ( r ` x ) , ( r ` y ) >. .x. ( s ` y ) ) ( ( x ( 2nd ` f ) y ) ` h ) ) = ( ( ( x ( 2nd ` g ) y ) ` h ) ( <. ( r ` x ) , ( s ` x ) >. .x. ( s ` y ) ) ( a ` x ) ) } )

  proof
    cN
    cC
    cD
    cnat
    co
    #
    vf
    vg
    cC
    cD
    cfunc
    co
    #
    @1
    vr
    vf
    cv
    #
    c1st
    cfv
    #
    vs
    vg
    cv
    #
    c1st
    cfv
    #
    vy
    cv
    #
    va
    cv
    #
    cfv
    #
    vh
    cv
    #
    vx
    cv
    #
    @6
    @2
    c2nd
    cfv
    co
    cfv
    #
    @10
    vr
    cv
    #
    cfv
    #
    @6
    @12
    cfv
    cop
    #
    @6
    vs
    cv
    #
    cfv
    #
    c.x
    co
    #
    co
    #
    @9
    @10
    @6
    @4
    c2nd
    cfv
    co
    cfv
    #
    @10
    @7
    cfv
    #
    @13
    @10
    @15
    cfv
    #
    cop
    #
    @16
    c.x
    co
    #
    co
    #
    wceq
    #
    vh
    @10
    @6
    cH
    co
    #
    wral
    #
    vy
    cB
    wral
    #
    vx
    cB
    wral
    #
    va
    vx
    cB
    @13
    @21
    cJ
    co
    #
    cixp
    #
    crab
    #
    csb
    #
    csb
    #
    cmpt2
    #
    natfval.1
    cC
    ccat
    wcel
    cD
    ccat
    wcel
    wa
    #
    @0
    @35
    wceq
    vt
    vu
    cC
    cD
    ccat
    ccat
    vf
    vg
    vt
    cv
    #
    vu
    cv
    #
    cfunc
    co
    #
    @39
    vr
    @3
    vs
    @5
    @8
    @11
    @14
    @16
    @38
    cco
    cfv
    #
    co
    #
    co
    #
    @19
    @20
    @22
    @16
    @40
    co
    #
    co
    #
    wceq
    #
    vh
    @10
    @6
    @37
    chom
    cfv
    #
    co
    #
    wral
    #
    vy
    @37
    cbs
    cfv
    #
    wral
    #
    vx
    @49
    wral
    #
    va
    vx
    @49
    @13
    @21
    @38
    chom
    cfv
    #
    co
    #
    cixp
    #
    crab
    #
    csb
    #
    csb
    #
    cmpt2
    #
    @35
    cnat
    @37
    cC
    wceq
    #
    @38
    cD
    wceq
    #
    wa
    #
    vf
    vg
    @39
    @39
    @57
    @1
    @1
    @34
    @37
    cC
    @38
    cD
    cfunc
    oveq12
    #
    @62
    @61
    vr
    @3
    @56
    @33
    @61
    vs
    @5
    @55
    @32
    @61
    @51
    @29
    va
    @54
    @31
    @61
    @54
    vx
    cB
    @53
    cixp
    @31
    @61
    vx
    @49
    cB
    @53
    @61
    @49
    cC
    cbs
    cfv
    cB
    @61
    @37
    cC
    cbs
    @59
    @60
    simpl
    #
    fveq2d
    natfval.b
    syl6eqr
    #
    ixpeq1d
    @61
    vx
    cB
    @53
    @30
    @61
    @52
    cJ
    @13
    @21
    @61
    @52
    cD
    chom
    cfv
    cJ
    @61
    @38
    cD
    chom
    @59
    @60
    simpr
    #
    fveq2d
    natfval.j
    syl6eqr
    oveqd
    ixpeq2dv
    eqtrd
    @61
    @50
    @28
    vx
    @49
    cB
    @64
    @61
    @48
    @27
    vy
    @49
    cB
    @64
    @61
    @45
    @25
    vh
    @47
    @26
    @61
    @46
    cH
    @10
    @6
    @61
    @46
    cC
    chom
    cfv
    cH
    @61
    @37
    cC
    chom
    @63
    fveq2d
    natfval.h
    syl6eqr
    oveqd
    @61
    @42
    @18
    @44
    @24
    @61
    @41
    @17
    @8
    @11
    @61
    @40
    c.x
    @14
    @16
    @61
    @40
    cD
    cco
    cfv
    c.x
    @61
    @38
    cD
    cco
    @65
    fveq2d
    natfval.o
    syl6eqr
    #
    oveqd
    oveqd
    @61
    @43
    @23
    @19
    @20
    @61
    @40
    c.x
    @22
    @16
    @66
    oveqd
    oveqd
    eqeq12d
    raleqbidv
    raleqbidv
    raleqbidv
    rabeqbidv
    csbeq2dv
    csbeq2dv
    mpt2eq123dv
    vx
    vy
    vu
    vt
    vf
    vg
    vh
    vs
    vr
    va
    df-nat
    #
    vf
    vg
    @1
    @1
    @34
    cC
    cD
    cfunc
    ovex
    #
    @68
    mpt2ex
    ovmpt2a
    @36
    wn
    #
    @0
    c0
    @35
    vt
    vu
    @58
    cnat
    cC
    cD
    ccat
    ccat
    @67
    mpt2ndm0
    @69
    @35
    vf
    vg
    c0
    c0
    @34
    cmpt2
    #
    c0
    @69
    @1
    c0
    wceq
    #
    @71
    @35
    @70
    wceq
    @69
    vf
    @1
    @2
    @1
    wcel
    @36
    cC
    cD
    @2
    funcrcl
    con3i
    eq0rdv
    #
    @72
    vf
    vg
    @1
    @1
    c0
    c0
    @34
    mpt2eq12
    syl2anc
    vf
    vg
    c0
    @34
    mpt20
    syl6eq
    eqtr4d
    pm2.61i
    eqtri
end
