include "cevlf.mm"
include "co.mm"
include "cfunc.mm"
include "cv.mm"
include "c1st.mm"
include "cfv.mm"
include "cmpt2.mm"
include "cxp.mm"
include "c2nd.mm"
include "cop.mm"
include "csb.mm"
include "ccat.mm"
include "cbs.mm"
include "cnat.mm"
include "chom.mm"
include "cco.mm"
include "cvv.mm"
include "wceq.mm"
include "df-evlf.mm"
include "a1i.mm"
include "wa.mm"
include "simprl.mm"
include "simprr.mm"
include "oveq12d.mm"
include "fveq2d.mm"
include "syl6eqr.mm"
include "eqidd.mm"
include "mpt2eq123dv.mm"
include "xpeq12d.mm"
include "oveqd.mm"
include "csbeq2dv.mm"
include "opeq12d.mm"
include "wcel.mm"
include "opex.mm"
include "ovmpt2d.mm"
include "syl5eq.mm"

theorem evlfval
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cC: class C
  let cD: class D
  let c.x: class .x.
  let vf: setvar f
  let vg: setvar g
  let vm: setvar m
  let vn: setvar n
  let cE: class E
  let cH: class H
  let cN: class N
  let va: setvar a
  let vc: setvar c
  let vd: setvar d
  let ve: setvar e
  let vz: setvar z
  let cF: class F
  let cG: class G
  let cA: class A
  let cX: class X
  let cY: class Y
  let cK: class K
  assume evlfval.e: |- E = ( C evalF D )
  assume evlfval.c: |- ( ph -> C e. Cat )
  assume evlfval.d: |- ( ph -> D e. Cat )
  assume evlfval.b: |- B = ( Base ` C )
  assume evlfval.h: |- H = ( Hom ` C )
  assume evlfval.o: |- .x. = ( comp ` D )
  assume evlfval.n: |- N = ( C Nat D )

  disjoint a f
  disjoint a g
  disjoint a m
  disjoint a n
  disjoint a x
  disjoint a y
  disjoint C a
  disjoint f g
  disjoint f m
  disjoint f n
  disjoint f x
  disjoint f y
  disjoint C f
  disjoint g m
  disjoint g n
  disjoint g x
  disjoint g y
  disjoint C g
  disjoint m n
  disjoint m x
  disjoint m y
  disjoint C m
  disjoint n x
  disjoint n y
  disjoint C n
  disjoint x y
  disjoint C x
  disjoint C y
  disjoint D a
  disjoint D f
  disjoint D g
  disjoint D m
  disjoint D n
  disjoint D x
  disjoint D y
  disjoint H g
  disjoint H m
  disjoint H n
  disjoint H x
  disjoint H y
  disjoint N a
  disjoint N g
  disjoint N m
  disjoint N n
  disjoint N x
  disjoint N y
  disjoint a ph
  disjoint f ph
  disjoint g ph
  disjoint m ph
  disjoint n ph
  disjoint ph x
  disjoint ph y
  disjoint .x. a
  disjoint .x. g
  disjoint .x. m
  disjoint .x. n
  disjoint .x. x
  disjoint .x. y
  disjoint B x
  disjoint B y
  disjoint a c
  disjoint a d
  disjoint c d
  disjoint c f
  disjoint c g
  disjoint c m
  disjoint c n
  disjoint c x
  disjoint c y
  disjoint C c
  disjoint d f
  disjoint d g
  disjoint d m
  disjoint d n
  disjoint d x
  disjoint d y
  disjoint C d
  disjoint D c
  disjoint D d
  disjoint H c
  disjoint H d
  disjoint a e
  disjoint a z
  disjoint c e
  disjoint c z
  disjoint d e
  disjoint d z
  disjoint e f
  disjoint e g
  disjoint e m
  disjoint e n
  disjoint e x
  disjoint e y
  disjoint e z
  disjoint f z
  disjoint g z
  disjoint m z
  disjoint n z
  disjoint x z
  disjoint y z
  disjoint F a
  disjoint F g
  disjoint F m
  disjoint F n
  disjoint F x
  disjoint F y
  disjoint N c
  disjoint N d
  disjoint G a
  disjoint G g
  disjoint G m
  disjoint G n
  disjoint G x
  disjoint G y
  disjoint c ph
  disjoint d ph
  disjoint .x. c
  disjoint .x. d
  disjoint A a
  disjoint A g
  disjoint B c
  disjoint B d
  disjoint X a
  disjoint X g
  disjoint X m
  disjoint X n
  disjoint X x
  disjoint X y
  disjoint Y a
  disjoint Y g
  disjoint Y m
  disjoint Y n
  disjoint Y x
  disjoint Y y
  disjoint K a
  disjoint K g
  assert |- ( ph -> E = <. ( f e. ( C Func D ) , x e. B |-> ( ( 1st ` f ) ` x ) ) , ( x e. ( ( C Func D ) X. B ) , y e. ( ( C Func D ) X. B ) |-> [_ ( 1st ` x ) / m ]_ [_ ( 1st ` y ) / n ]_ ( a e. ( m N n ) , g e. ( ( 2nd ` x ) H ( 2nd ` y ) ) |-> ( ( a ` ( 2nd ` y ) ) ( <. ( ( 1st ` m ) ` ( 2nd ` x ) ) , ( ( 1st ` m ) ` ( 2nd ` y ) ) >. .x. ( ( 1st ` n ) ` ( 2nd ` y ) ) ) ( ( ( 2nd ` x ) ( 2nd ` m ) ( 2nd ` y ) ) ` g ) ) ) ) >. )

  proof
    wph
    cE
    cC
    cD
    cevlf
    co
    vf
    vx
    cC
    cD
    cfunc
    co
    #
    cB
    vx
    cv
    #
    vf
    cv
    c1st
    cfv
    cfv
    #
    cmpt2
    #
    vx
    vy
    @0
    cB
    cxp
    #
    @4
    vm
    @1
    c1st
    cfv
    #
    vn
    vy
    cv
    #
    c1st
    cfv
    #
    va
    vg
    vm
    cv
    #
    vn
    cv
    #
    cN
    co
    #
    @1
    c2nd
    cfv
    #
    @6
    c2nd
    cfv
    #
    cH
    co
    #
    @12
    va
    cv
    cfv
    #
    vg
    cv
    @11
    @12
    @8
    c2nd
    cfv
    co
    cfv
    #
    @11
    @8
    c1st
    cfv
    #
    cfv
    @12
    @16
    cfv
    cop
    #
    @12
    @9
    c1st
    cfv
    cfv
    #
    c.x
    co
    #
    co
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
    evlfval.e
    wph
    vc
    vd
    cC
    cD
    ccat
    ccat
    vf
    vx
    vc
    cv
    #
    vd
    cv
    #
    cfunc
    co
    #
    @26
    cbs
    cfv
    #
    @2
    cmpt2
    #
    vx
    vy
    @28
    @29
    cxp
    #
    @31
    vm
    @5
    vn
    @7
    va
    vg
    @8
    @9
    @26
    @27
    cnat
    co
    #
    co
    #
    @11
    @12
    @26
    chom
    cfv
    #
    co
    #
    @14
    @15
    @17
    @18
    @27
    cco
    cfv
    #
    co
    #
    co
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
    @25
    cevlf
    cvv
    cevlf
    vc
    vd
    ccat
    ccat
    @43
    cmpt2
    wceq
    wph
    vx
    vy
    vf
    vg
    vm
    vn
    va
    vc
    vd
    df-evlf
    a1i
    wph
    @26
    cC
    wceq
    #
    @27
    cD
    wceq
    #
    wa
    wa
    #
    @30
    @3
    @42
    @24
    @46
    vf
    vx
    @28
    @29
    @2
    @0
    cB
    @2
    @46
    @26
    cC
    @27
    cD
    cfunc
    wph
    @44
    @45
    simprl
    #
    wph
    @44
    @45
    simprr
    #
    oveq12d
    #
    @46
    @29
    cC
    cbs
    cfv
    cB
    @46
    @26
    cC
    cbs
    @47
    fveq2d
    evlfval.b
    syl6eqr
    #
    @46
    @2
    eqidd
    mpt2eq123dv
    @46
    vx
    vy
    @31
    @31
    @41
    @4
    @4
    @23
    @46
    @28
    @0
    @29
    cB
    @49
    @50
    xpeq12d
    #
    @51
    @46
    vm
    @5
    @40
    @22
    @46
    vn
    @7
    @39
    @21
    @46
    va
    vg
    @33
    @35
    @38
    @10
    @13
    @20
    @46
    @32
    cN
    @8
    @9
    @46
    @32
    cC
    cD
    cnat
    co
    cN
    @46
    @26
    cC
    @27
    cD
    cnat
    @47
    @48
    oveq12d
    evlfval.n
    syl6eqr
    oveqd
    @46
    @34
    cH
    @11
    @12
    @46
    @34
    cC
    chom
    cfv
    cH
    @46
    @26
    cC
    chom
    @47
    fveq2d
    evlfval.h
    syl6eqr
    oveqd
    @46
    @37
    @19
    @14
    @15
    @46
    @36
    c.x
    @17
    @18
    @46
    @36
    cD
    cco
    cfv
    c.x
    @46
    @27
    cD
    cco
    @48
    fveq2d
    evlfval.o
    syl6eqr
    oveqd
    oveqd
    mpt2eq123dv
    csbeq2dv
    csbeq2dv
    mpt2eq123dv
    opeq12d
    evlfval.c
    evlfval.d
    @25
    cvv
    wcel
    wph
    @3
    @24
    opex
    a1i
    ovmpt2d
    syl5eq
end
