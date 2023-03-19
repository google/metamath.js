include "cvv.mm"
include "wcel.mm"
include "wa.mm"
include "cxp.mm"
include "cv.mm"
include "c2nd.mm"
include "cfv.mm"
include "co.mm"
include "c1st.mm"
include "cop.mm"
include "cmpt2.mm"
include "wceq.mm"
include "cnx.mm"
include "cbs.mm"
include "chom.mm"
include "cco.mm"
include "ctp.mm"
include "c1.mm"
include "c5.mm"
include "cdc.mm"
include "eqid.mm"
include "simpl.mm"
include "simpr.mm"
include "xpcbas.mm"
include "eqtr4i.mm"
include "a1i.mm"
include "xpchomfval.mm"
include "eqidd.mm"
include "xpcval.mm"
include "catstr.mm"
include "ccoid.mm"
include "snsstp3.mm"
include "fvex.mm"
include "eqeltri.mm"
include "xpex.mm"
include "mpt2ex.mm"
include "strfv3.mm"
include "wn.mm"
include "c0.mm"
include "mpt20.mm"
include "eqcomi.mm"
include "cxpc.mm"
include "wfn.mm"
include "cdm.mm"
include "fnxpc.mm"
include "fndm.mm"
include "ax-mp.mm"
include "ndmov.mm"
include "syl5eq.mm"
include "fveq2d.mm"
include "str0.mm"
include "3eqtr4g.mm"
include "base0.mm"
include "xpeq2d.mm"
include "xp0.mm"
include "syl6eq.mm"
include "mpt2eq123dv.mm"
include "3eqtr4a.mm"
include "pm2.61i.mm"

theorem xpccofval
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cC: class C
  let cD: class D
  let c.xb: class .xb
  let cT: class T
  let c.x: class .x.
  let vf: setvar f
  let vg: setvar g
  let cK: class K
  let cO: class O
  let vu: setvar u
  let vv: setvar v
  let cF: class F
  let wph: wff ph
  let cG: class G
  let cX: class X
  let cY: class Y
  let cZ: class Z
  assume xpccofval.t: |- T = ( C Xc. D )
  assume xpccofval.b: |- B = ( Base ` T )
  assume xpccofval.k: |- K = ( Hom ` T )
  assume xpccofval.o1: |- .x. = ( comp ` C )
  assume xpccofval.o2: |- .xb = ( comp ` D )
  assume xpccofval.o: |- O = ( comp ` T )

  disjoint f g
  disjoint f x
  disjoint f y
  disjoint B f
  disjoint g x
  disjoint g y
  disjoint B g
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint C f
  disjoint C g
  disjoint C x
  disjoint C y
  disjoint D f
  disjoint D g
  disjoint D x
  disjoint D y
  disjoint .x. f
  disjoint .x. g
  disjoint .x. x
  disjoint .x. y
  disjoint .xb f
  disjoint .xb g
  disjoint .xb x
  disjoint .xb y
  disjoint K f
  disjoint K g
  disjoint K x
  disjoint K y
  disjoint O x
  disjoint O y
  disjoint f u
  disjoint f v
  disjoint g u
  disjoint g v
  disjoint u v
  disjoint u x
  disjoint u y
  disjoint B u
  disjoint v x
  disjoint v y
  disjoint B v
  disjoint C u
  disjoint C v
  disjoint F f
  disjoint F g
  disjoint F x
  disjoint F y
  disjoint f ph
  disjoint g ph
  disjoint ph x
  disjoint ph y
  disjoint D u
  disjoint D v
  disjoint G f
  disjoint G g
  disjoint G x
  disjoint G y
  disjoint X f
  disjoint X g
  disjoint X x
  disjoint X y
  disjoint Y f
  disjoint Y g
  disjoint Y x
  disjoint Y y
  disjoint Z f
  disjoint Z g
  disjoint Z x
  disjoint Z y
  assert |- O = ( x e. ( B X. B ) , y e. B |-> ( g e. ( ( 2nd ` x ) K y ) , f e. ( K ` x ) |-> <. ( ( 1st ` g ) ( <. ( 1st ` ( 1st ` x ) ) , ( 1st ` ( 2nd ` x ) ) >. .x. ( 1st ` y ) ) ( 1st ` f ) ) , ( ( 2nd ` g ) ( <. ( 2nd ` ( 1st ` x ) ) , ( 2nd ` ( 2nd ` x ) ) >. .xb ( 2nd ` y ) ) ( 2nd ` f ) ) >. ) )

  proof
    cC
    cvv
    wcel
    #
    cD
    cvv
    wcel
    #
    wa
    #
    cO
    vx
    vy
    cB
    cB
    cxp
    #
    cB
    vg
    vf
    vx
    cv
    #
    c2nd
    cfv
    #
    vy
    cv
    #
    cK
    co
    @4
    cK
    cfv
    vg
    cv
    #
    c1st
    cfv
    vf
    cv
    #
    c1st
    cfv
    @4
    c1st
    cfv
    #
    c1st
    cfv
    @5
    c1st
    cfv
    cop
    @6
    c1st
    cfv
    c.x
    co
    co
    @7
    c2nd
    cfv
    @8
    c2nd
    cfv
    @9
    c2nd
    cfv
    @5
    c2nd
    cfv
    cop
    @6
    c2nd
    cfv
    c.xb
    co
    co
    cop
    cmpt2
    #
    cmpt2
    #
    wceq
    @2
    cO
    @11
    cnx
    cbs
    cfv
    cB
    cop
    #
    cnx
    chom
    cfv
    cK
    cop
    #
    cnx
    cco
    cfv
    #
    @11
    cop
    #
    ctp
    cT
    cco
    cvv
    c1
    c1
    c5
    cdc
    cop
    @2
    vx
    vy
    vv
    vu
    cB
    cC
    cD
    c.xb
    cT
    c.x
    vf
    vg
    cC
    chom
    cfv
    #
    cD
    chom
    cfv
    #
    cK
    @11
    cvv
    cvv
    cC
    cbs
    cfv
    #
    cD
    cbs
    cfv
    #
    xpccofval.t
    @18
    eqid
    #
    @19
    eqid
    #
    @16
    eqid
    #
    @17
    eqid
    #
    xpccofval.o1
    xpccofval.o2
    @0
    @1
    simpl
    @0
    @1
    simpr
    cB
    @18
    @19
    cxp
    #
    wceq
    @2
    cB
    cT
    cbs
    cfv
    #
    @24
    xpccofval.b
    cC
    cD
    cT
    @18
    @19
    xpccofval.t
    @20
    @21
    xpcbas
    eqtr4i
    a1i
    cK
    vu
    vv
    cB
    cB
    vu
    cv
    #
    c1st
    cfv
    vv
    cv
    #
    c1st
    cfv
    @16
    co
    @26
    c2nd
    cfv
    @27
    c2nd
    cfv
    @17
    co
    cxp
    cmpt2
    wceq
    @2
    vv
    vu
    cB
    cC
    cD
    cT
    @16
    @17
    cK
    xpccofval.t
    xpccofval.b
    @22
    @23
    xpccofval.k
    xpchomfval
    a1i
    @2
    @11
    eqidd
    xpcval
    @11
    cB
    cK
    catstr
    ccoid
    @12
    @13
    @15
    snsstp3
    @11
    cvv
    wcel
    @2
    vx
    vy
    @3
    cB
    @10
    cB
    cB
    cB
    @25
    cvv
    xpccofval.b
    cT
    cbs
    fvex
    eqeltri
    #
    @28
    xpex
    @28
    mpt2ex
    a1i
    xpccofval.o
    strfv3
    @2
    wn
    #
    c0
    vx
    vy
    c0
    c0
    @10
    cmpt2
    #
    cO
    @11
    @30
    c0
    vx
    vy
    c0
    @10
    mpt20
    eqcomi
    @29
    cT
    cco
    cfv
    c0
    cco
    cfv
    cO
    c0
    @29
    cT
    c0
    cco
    @29
    cT
    cC
    cD
    cxpc
    co
    c0
    xpccofval.t
    cC
    cD
    cvv
    cxpc
    cxpc
    cvv
    cvv
    cxp
    #
    wfn
    cxpc
    cdm
    @31
    wceq
    fnxpc
    @31
    cxpc
    fndm
    ax-mp
    ndmov
    syl5eq
    #
    fveq2d
    xpccofval.o
    cco
    @14
    ccoid
    str0
    3eqtr4g
    @29
    vx
    vy
    @3
    cB
    @10
    c0
    c0
    @10
    @29
    @3
    cB
    c0
    cxp
    c0
    @29
    cB
    c0
    cB
    @29
    @25
    c0
    cbs
    cfv
    cB
    c0
    @29
    cT
    c0
    cbs
    @32
    fveq2d
    xpccofval.b
    base0
    3eqtr4g
    #
    xpeq2d
    cB
    xp0
    syl6eq
    @33
    @29
    @10
    eqidd
    mpt2eq123dv
    3eqtr4a
    pm2.61i
end
