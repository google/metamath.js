include "c1st.mm"
include "cfv.mm"
include "co.mm"
include "cop.mm"
include "c2nd.mm"
include "ctpos.mm"
include "c2ndf.mm"
include "ccofu.mm"
include "c1stf.mm"
include "cprf.mm"
include "cnat.mm"
include "fveq2i.mm"
include "oveqi.mm"
include "df-ov.mm"
include "eqtri.mm"
include "cfunc.mm"
include "cxp.mm"
include "cxpc.mm"
include "coppc.mm"
include "eqid.mm"
include "fucbas.mm"
include "oppcbas.mm"
include "xpcbas.mm"
include "ccat.mm"
include "wcel.mm"
include "oppccat.mm"
include "syl.mm"
include "cvv.mm"
include "chomf.mm"
include "crn.mm"
include "unssbd.mm"
include "ssexd.mm"
include "setccat.mm"
include "fuccat.mm"
include "2ndfcl.mm"
include "wbr.mm"
include "wrel.mm"
include "relfunc.mm"
include "yoncl.mm"
include "1st2ndbr.mm"
include "sylancr.mm"
include "funcoppc.mm"
include "df-br.mm"
include "sylib.mm"
include "cofucl.mm"
include "1stfcl.mm"
include "prfcl.mm"
include "unssad.mm"
include "hofcl.mm"
include "opelxpi.mm"
include "syl2anc.mm"
include "cofu1.mm"
include "syl5eq.mm"
include "chom.mm"
include "prf1.mm"
include "wceq.mm"
include "fvex.mm"
include "tposex.mm"
include "op1st.mm"
include "a1i.mm"
include "2ndf1.mm"
include "op2ndg.mm"
include "eqtrd.mm"
include "fveq12d.mm"
include "1stf1.mm"
include "op1stg.mm"
include "opeq12d.mm"
include "fveq2d.mm"
include "syl6eqr.mm"
include "fuchom.mm"
include "yon1cl.mm"
include "hof1.mm"
include "3eqtrd.mm"

theorem yonedalem21
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cQ: class Q
  let cR: class R
  let cS: class S
  let cT: class T
  let cU: class U
  let c.1: class .1.
  let cE: class E
  let cF: class F
  let cH: class H
  let cO: class O
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let va: setvar a
  let vb: setvar b
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let vh: setvar h
  let vk: setvar k
  let vu: setvar u
  let vw: setvar w
  let vz: setvar z
  let cA: class A
  let vv: setvar v
  let cK: class K
  let cG: class G
  let cN: class N
  let cI: class I
  let cM: class M
  let cP: class P
  assume yoneda.y: |- Y = ( Yon ` C )
  assume yoneda.b: |- B = ( Base ` C )
  assume yoneda.1: |- .1. = ( Id ` C )
  assume yoneda.o: |- O = ( oppCat ` C )
  assume yoneda.s: |- S = ( SetCat ` U )
  assume yoneda.t: |- T = ( SetCat ` V )
  assume yoneda.q: |- Q = ( O FuncCat S )
  assume yoneda.h: |- H = ( HomF ` Q )
  assume yoneda.r: |- R = ( ( Q Xc. O ) FuncCat T )
  assume yoneda.e: |- E = ( O evalF S )
  assume yoneda.z: |- Z = ( H o.func ( ( <. ( 1st ` Y ) , tpos ( 2nd ` Y ) >. o.func ( Q 2ndF O ) ) pairF ( Q 1stF O ) ) )
  assume yoneda.c: |- ( ph -> C e. Cat )
  assume yoneda.w: |- ( ph -> V e. W )
  assume yoneda.u: |- ( ph -> ran ( Homf ` C ) C_ U )
  assume yoneda.v: |- ( ph -> ( ran ( Homf ` Q ) u. U ) C_ V )
  assume yonedalem21.f: |- ( ph -> F e. ( O Func S ) )
  assume yonedalem21.x: |- ( ph -> X e. B )


  assert |- ( ph -> ( F ( 1st ` Z ) X ) = ( ( ( 1st ` Y ) ` X ) ( O Nat S ) F ) )

  proof
    wph
    cF
    cX
    cZ
    c1st
    cfv
    #
    co
    #
    cF
    cX
    cop
    #
    cY
    c1st
    cfv
    #
    cY
    c2nd
    cfv
    #
    ctpos
    #
    cop
    #
    cQ
    cO
    c2ndf
    co
    #
    ccofu
    co
    #
    cQ
    cO
    c1stf
    co
    #
    cprf
    co
    #
    c1st
    cfv
    cfv
    #
    cH
    c1st
    cfv
    #
    cfv
    #
    cX
    @3
    cfv
    #
    cF
    @12
    co
    #
    @14
    cF
    cO
    cS
    cnat
    co
    #
    co
    wph
    @1
    @2
    cH
    @10
    ccofu
    co
    #
    c1st
    cfv
    #
    cfv
    #
    @13
    @1
    cF
    cX
    @18
    co
    @19
    @0
    @18
    cF
    cX
    cZ
    @17
    c1st
    yoneda.z
    fveq2i
    oveqi
    cF
    cX
    @18
    df-ov
    eqtri
    wph
    cO
    cS
    cfunc
    co
    #
    cB
    cxp
    #
    cQ
    cO
    cxpc
    co
    #
    cQ
    coppc
    cfv
    #
    cQ
    cxpc
    co
    #
    cT
    @10
    cH
    @2
    cQ
    cO
    @22
    @20
    cB
    @22
    eqid
    #
    cO
    cS
    cQ
    yoneda.q
    fucbas
    #
    cB
    cC
    cO
    yoneda.o
    yoneda.b
    oppcbas
    xpcbas
    #
    wph
    @22
    @23
    @10
    @24
    cQ
    @8
    @9
    @10
    eqid
    #
    @24
    eqid
    wph
    @22
    cO
    @23
    @7
    @6
    wph
    cQ
    cO
    @7
    @22
    @25
    wph
    cO
    cS
    cQ
    yoneda.q
    wph
    cC
    ccat
    wcel
    cO
    ccat
    wcel
    yoneda.c
    cC
    cO
    yoneda.o
    oppccat
    syl
    #
    wph
    cU
    cvv
    wcel
    cS
    ccat
    wcel
    wph
    cU
    cV
    cW
    yoneda.w
    wph
    cQ
    chomf
    cfv
    crn
    #
    cU
    cV
    yoneda.v
    unssbd
    ssexd
    #
    cS
    cU
    cvv
    yoneda.s
    setccat
    syl
    fuccat
    #
    @29
    @7
    eqid
    #
    2ndfcl
    #
    wph
    @3
    @5
    cO
    @23
    cfunc
    co
    #
    wbr
    @6
    @35
    wcel
    wph
    cC
    cQ
    @23
    @3
    @4
    cO
    yoneda.o
    @23
    eqid
    #
    wph
    cC
    cQ
    cfunc
    co
    #
    wrel
    cY
    @37
    wcel
    @3
    @4
    @37
    wbr
    cC
    cQ
    relfunc
    wph
    cC
    cQ
    cS
    cU
    cO
    cvv
    cY
    yoneda.y
    yoneda.c
    yoneda.o
    yoneda.s
    yoneda.q
    @31
    yoneda.u
    yoncl
    cY
    @37
    1st2ndbr
    sylancr
    funcoppc
    @3
    @5
    @35
    df-br
    sylib
    #
    cofucl
    #
    wph
    cQ
    cO
    @9
    @22
    @25
    @32
    @29
    @9
    eqid
    #
    1stfcl
    #
    prfcl
    wph
    cQ
    cT
    cV
    cH
    @23
    cW
    yoneda.h
    @36
    yoneda.t
    @32
    yoneda.w
    wph
    @30
    cU
    cV
    yoneda.v
    unssad
    hofcl
    wph
    cF
    @20
    wcel
    #
    cX
    cB
    wcel
    #
    @2
    @21
    wcel
    yonedalem21.f
    yonedalem21.x
    cF
    cX
    @20
    cB
    opelxpi
    syl2anc
    #
    cofu1
    syl5eq
    wph
    @13
    @14
    cF
    cop
    #
    @12
    cfv
    @15
    wph
    @11
    @45
    @12
    wph
    @11
    @2
    @8
    c1st
    cfv
    cfv
    #
    @2
    @9
    c1st
    cfv
    cfv
    #
    cop
    @45
    wph
    @21
    @22
    @23
    @10
    cQ
    @8
    @9
    @22
    chom
    cfv
    #
    @2
    @28
    @27
    @48
    eqid
    #
    @39
    @41
    @44
    prf1
    wph
    @46
    @14
    @47
    cF
    wph
    @46
    @2
    @7
    c1st
    cfv
    cfv
    #
    @6
    c1st
    cfv
    #
    cfv
    @14
    wph
    @21
    @22
    cO
    @23
    @7
    @6
    @2
    @27
    @34
    @38
    @44
    cofu1
    wph
    @50
    cX
    @51
    @3
    @51
    @3
    wceq
    wph
    @3
    @5
    cY
    c1st
    fvex
    @4
    cY
    c2nd
    fvex
    tposex
    op1st
    a1i
    wph
    @50
    @2
    c2nd
    cfv
    #
    cX
    wph
    @21
    cQ
    cO
    @7
    @2
    @22
    @48
    @25
    @27
    @49
    @32
    @29
    @33
    @44
    2ndf1
    wph
    @42
    @43
    @52
    cX
    wceq
    yonedalem21.f
    yonedalem21.x
    cF
    cX
    @20
    cB
    op2ndg
    syl2anc
    eqtrd
    fveq12d
    eqtrd
    wph
    @47
    @2
    c1st
    cfv
    #
    cF
    wph
    @21
    cQ
    cO
    @9
    @2
    @22
    @48
    @25
    @27
    @49
    @32
    @29
    @40
    @44
    1stf1
    wph
    @42
    @43
    @53
    cF
    wceq
    yonedalem21.f
    yonedalem21.x
    cF
    cX
    @20
    cB
    op1stg
    syl2anc
    eqtrd
    opeq12d
    eqtrd
    fveq2d
    @14
    cF
    @12
    df-ov
    syl6eqr
    wph
    @20
    cQ
    @16
    cH
    @14
    cF
    yoneda.h
    @32
    @26
    cO
    cS
    cQ
    @16
    yoneda.q
    @16
    eqid
    fuchom
    wph
    cB
    cC
    cS
    cU
    cO
    cvv
    cX
    cY
    yoneda.y
    yoneda.b
    yoneda.c
    yonedalem21.x
    yoneda.o
    yoneda.s
    @31
    yoneda.u
    yon1cl
    yonedalem21.f
    hof1
    3eqtrd
end
