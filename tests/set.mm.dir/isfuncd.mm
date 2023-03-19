include "cfunc.mm"
include "co.mm"
include "wbr.mm"
include "wf.mm"
include "cxp.mm"
include "cv.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "cmap.mm"
include "cixp.mm"
include "wcel.mm"
include "wceq.mm"
include "cop.mm"
include "wral.mm"
include "wa.mm"
include "cvv.mm"
include "wfn.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "xpex.mm"
include "fnex.mm"
include "sylancl.mm"
include "ovex.mm"
include "elmap.mm"
include "sylibr.mm"
include "ralrimivva.mm"
include "fveq2.mm"
include "df-ov.mm"
include "syl6eqr.mm"
include "vex.mm"
include "op1std.mm"
include "fveq2d.mm"
include "op2ndd.mm"
include "oveq12d.mm"
include "eleq12d.mm"
include "ralxp.mm"
include "elixp2.mm"
include "syl3anbrc.mm"
include "wi.mm"
include "w3a.mm"
include "3expia.mm"
include "3exp2.mm"
include "imp43.mm"
include "ralrimivv.mm"
include "jca.mm"
include "ralrimiva.mm"
include "isfunc.mm"
include "mpbir3and.mm"

theorem isfuncd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cC: class C
  let cD: class D
  let c.x: class .x.
  let c.1: class .1.
  let vm: setvar m
  let vn: setvar n
  let cE: class E
  let cF: class F
  let cG: class G
  let cH: class H
  let cI: class I
  let cJ: class J
  let cO: class O
  let vb: setvar b
  let vd: setvar d
  let ve: setvar e
  let vf: setvar f
  let vg: setvar g
  assume isfunc.b: |- B = ( Base ` D )
  assume isfunc.c: |- C = ( Base ` E )
  assume isfunc.h: |- H = ( Hom ` D )
  assume isfunc.j: |- J = ( Hom ` E )
  assume isfunc.1: |- .1. = ( Id ` D )
  assume isfunc.i: |- I = ( Id ` E )
  assume isfunc.x: |- .x. = ( comp ` D )
  assume isfunc.o: |- O = ( comp ` E )
  assume isfunc.d: |- ( ph -> D e. Cat )
  assume isfunc.e: |- ( ph -> E e. Cat )
  assume isfuncd.1: |- ( ph -> F : B --> C )
  assume isfuncd.2: |- ( ph -> G Fn ( B X. B ) )
  assume isfuncd.3: |- ( ( ph /\ ( x e. B /\ y e. B ) ) -> ( x G y ) : ( x H y ) --> ( ( F ` x ) J ( F ` y ) ) )
  assume isfuncd.4: |- ( ( ph /\ x e. B ) -> ( ( x G x ) ` ( .1. ` x ) ) = ( I ` ( F ` x ) ) )
  assume isfuncd.5: |- ( ( ph /\ ( x e. B /\ y e. B /\ z e. B ) /\ ( m e. ( x H y ) /\ n e. ( y H z ) ) ) -> ( ( x G z ) ` ( n ( <. x , y >. .x. z ) m ) ) = ( ( ( y G z ) ` n ) ( <. ( F ` x ) , ( F ` y ) >. O ( F ` z ) ) ( ( x G y ) ` m ) ) )

  disjoint m n
  disjoint m x
  disjoint m y
  disjoint m z
  disjoint B m
  disjoint n x
  disjoint n y
  disjoint n z
  disjoint B n
  disjoint x y
  disjoint x z
  disjoint B x
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint D m
  disjoint D n
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint E m
  disjoint E n
  disjoint E x
  disjoint E y
  disjoint E z
  disjoint H m
  disjoint H n
  disjoint H x
  disjoint H y
  disjoint H z
  disjoint F m
  disjoint F n
  disjoint F x
  disjoint F y
  disjoint F z
  disjoint G m
  disjoint G n
  disjoint G x
  disjoint G y
  disjoint G z
  disjoint J x
  disjoint J y
  disjoint J z
  disjoint m ph
  disjoint n ph
  disjoint ph x
  disjoint ph y
  disjoint ph z
  disjoint b d
  disjoint b e
  disjoint b f
  disjoint b g
  disjoint b m
  disjoint b n
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint B b
  disjoint d e
  disjoint d f
  disjoint d g
  disjoint d m
  disjoint d n
  disjoint d x
  disjoint d y
  disjoint d z
  disjoint B d
  disjoint e f
  disjoint e g
  disjoint e m
  disjoint e n
  disjoint e x
  disjoint e y
  disjoint e z
  disjoint B e
  disjoint f g
  disjoint f m
  disjoint f n
  disjoint f x
  disjoint f y
  disjoint f z
  disjoint B f
  disjoint g m
  disjoint g n
  disjoint g x
  disjoint g y
  disjoint g z
  disjoint B g
  disjoint C b
  disjoint C d
  disjoint C e
  disjoint C f
  disjoint C g
  disjoint D b
  disjoint D d
  disjoint D e
  disjoint D f
  disjoint D g
  disjoint E b
  disjoint E d
  disjoint E e
  disjoint E f
  disjoint E g
  disjoint H b
  disjoint H d
  disjoint H e
  disjoint H f
  disjoint H g
  disjoint I b
  disjoint I d
  disjoint I e
  disjoint I f
  disjoint I g
  disjoint F f
  disjoint F g
  disjoint G f
  disjoint G g
  disjoint J b
  disjoint J d
  disjoint J e
  disjoint J f
  disjoint J g
  disjoint .1. b
  disjoint .1. d
  disjoint .1. e
  disjoint .1. f
  disjoint .1. g
  disjoint .x. b
  disjoint .x. d
  disjoint .x. e
  disjoint .x. f
  disjoint .x. g
  disjoint O b
  disjoint O d
  disjoint O e
  disjoint O f
  disjoint O g
  assert |- ( ph -> F ( D Func E ) G )

  proof
    wph
    cF
    cG
    cD
    cE
    cfunc
    co
    wbr
    cB
    cC
    cF
    wf
    cG
    vz
    cB
    cB
    cxp
    #
    vz
    cv
    #
    c1st
    cfv
    #
    cF
    cfv
    #
    @1
    c2nd
    cfv
    #
    cF
    cfv
    #
    cJ
    co
    #
    @1
    cH
    cfv
    #
    cmap
    co
    #
    cixp
    wcel
    #
    vx
    cv
    #
    c.1
    cfv
    @10
    @10
    cG
    co
    cfv
    @10
    cF
    cfv
    #
    cI
    cfv
    wceq
    #
    vn
    cv
    #
    vm
    cv
    #
    @10
    vy
    cv
    #
    cop
    #
    @1
    c.x
    co
    co
    @10
    @1
    cG
    co
    cfv
    @13
    @15
    @1
    cG
    co
    cfv
    @14
    @10
    @15
    cG
    co
    #
    cfv
    @11
    @15
    cF
    cfv
    #
    cop
    @1
    cF
    cfv
    cO
    co
    co
    wceq
    #
    vn
    @15
    @1
    cH
    co
    #
    wral
    vm
    @10
    @15
    cH
    co
    #
    wral
    #
    vz
    cB
    wral
    vy
    cB
    wral
    #
    wa
    #
    vx
    cB
    wral
    isfuncd.1
    wph
    cG
    cvv
    wcel
    #
    cG
    @0
    wfn
    #
    @1
    cG
    cfv
    #
    @8
    wcel
    #
    vz
    @0
    wral
    #
    @9
    wph
    @26
    @0
    cvv
    wcel
    @25
    isfuncd.2
    cB
    cB
    cB
    cD
    cbs
    cfv
    cvv
    isfunc.b
    cD
    cbs
    fvex
    eqeltri
    #
    @30
    xpex
    @0
    cvv
    cG
    fnex
    sylancl
    isfuncd.2
    wph
    @17
    @11
    @18
    cJ
    co
    #
    @21
    cmap
    co
    #
    wcel
    #
    vy
    cB
    wral
    vx
    cB
    wral
    @29
    wph
    @33
    vx
    vy
    cB
    cB
    wph
    @10
    cB
    wcel
    #
    @15
    cB
    wcel
    #
    wa
    wa
    @21
    @31
    @17
    wf
    @33
    isfuncd.3
    @31
    @21
    @17
    @11
    @18
    cJ
    ovex
    @10
    @15
    cH
    ovex
    elmap
    sylibr
    ralrimivva
    @28
    @33
    vz
    vx
    vy
    cB
    cB
    @1
    @16
    wceq
    #
    @27
    @17
    @8
    @32
    @36
    @27
    @16
    cG
    cfv
    @17
    @1
    @16
    cG
    fveq2
    @10
    @15
    cG
    df-ov
    syl6eqr
    @36
    @6
    @31
    @7
    @21
    cmap
    @36
    @3
    @11
    @5
    @18
    cJ
    @36
    @2
    @10
    cF
    @10
    @15
    @1
    vx
    vex
    #
    vy
    vex
    #
    op1std
    fveq2d
    @36
    @4
    @15
    cF
    @10
    @15
    @1
    @37
    @38
    op2ndd
    fveq2d
    oveq12d
    @36
    @7
    @16
    cH
    cfv
    @21
    @1
    @16
    cH
    fveq2
    @10
    @15
    cH
    df-ov
    syl6eqr
    oveq12d
    eleq12d
    ralxp
    sylibr
    vz
    @0
    @8
    cG
    elixp2
    syl3anbrc
    wph
    @24
    vx
    cB
    wph
    @34
    wa
    #
    @12
    @23
    isfuncd.4
    @39
    @22
    vy
    vz
    cB
    cB
    @39
    @35
    @1
    cB
    wcel
    #
    wa
    wa
    @19
    vm
    vn
    @21
    @20
    wph
    @34
    @35
    @40
    @14
    @21
    wcel
    @13
    @20
    wcel
    wa
    #
    @19
    wi
    #
    wph
    @34
    @35
    @40
    @42
    wph
    @34
    @35
    @40
    w3a
    @41
    @19
    isfuncd.5
    3expia
    3exp2
    imp43
    ralrimivv
    ralrimivva
    jca
    ralrimiva
    wph
    vx
    vy
    vz
    cB
    cC
    cD
    c.x
    c.1
    vm
    vn
    cE
    cF
    cG
    cH
    cI
    cJ
    cO
    isfunc.b
    isfunc.c
    isfunc.h
    isfunc.j
    isfunc.1
    isfunc.i
    isfunc.x
    isfunc.o
    isfunc.d
    isfunc.e
    isfunc
    mpbir3and
end
