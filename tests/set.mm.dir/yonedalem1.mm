include "cxpc.mm"
include "co.mm"
include "cfunc.mm"
include "wcel.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "ctpos.mm"
include "cop.mm"
include "c2ndf.mm"
include "ccofu.mm"
include "c1stf.mm"
include "cprf.mm"
include "coppc.mm"
include "eqid.mm"
include "ccat.mm"
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
include "syl5eqel.mm"
include "funcsetcres2.mm"
include "evlfcl.mm"
include "sseldd.mm"
include "jca.mm"

theorem yonedalem1
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
  let cH: class H
  let cO: class O
  let cV: class V
  let cW: class W
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
  let cF: class F
  let cK: class K
  let cG: class G
  let cN: class N
  let cI: class I
  let cM: class M
  let cP: class P
  let cX: class X
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


  assert |- ( ph -> ( Z e. ( ( Q Xc. O ) Func T ) /\ E e. ( ( Q Xc. O ) Func T ) ) )

  proof
    wph
    cZ
    cQ
    cO
    cxpc
    co
    #
    cT
    cfunc
    co
    #
    wcel
    cE
    @1
    wcel
    wph
    cZ
    cH
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
    ccofu
    co
    @1
    yoneda.z
    wph
    @0
    cQ
    coppc
    cfv
    #
    cQ
    cxpc
    co
    #
    cT
    @9
    cH
    wph
    @0
    @10
    @9
    @11
    cQ
    @7
    @8
    @9
    eqid
    @11
    eqid
    wph
    @0
    cO
    @10
    @6
    @5
    wph
    cQ
    cO
    @6
    @0
    @0
    eqid
    #
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
    #
    ssexd
    #
    cS
    cU
    cvv
    yoneda.s
    setccat
    syl
    #
    fuccat
    #
    @13
    @6
    eqid
    2ndfcl
    wph
    @2
    @4
    cO
    @10
    cfunc
    co
    #
    wbr
    @5
    @19
    wcel
    wph
    cC
    cQ
    @10
    @2
    @3
    cO
    yoneda.o
    @10
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
    @21
    wcel
    @2
    @3
    @21
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
    @16
    yoneda.u
    yoncl
    cY
    @21
    1st2ndbr
    sylancr
    funcoppc
    @2
    @4
    @19
    df-br
    sylib
    cofucl
    wph
    cQ
    cO
    @8
    @0
    @12
    @18
    @13
    @8
    eqid
    1stfcl
    prfcl
    wph
    cQ
    cT
    cV
    cH
    @10
    cW
    yoneda.h
    @20
    yoneda.t
    @18
    yoneda.w
    wph
    @14
    cU
    cV
    yoneda.v
    unssad
    hofcl
    cofucl
    syl5eqel
    wph
    @0
    cS
    cfunc
    co
    @1
    cE
    wph
    cT
    cS
    cV
    @0
    cU
    cW
    yoneda.t
    yoneda.s
    yoneda.w
    @15
    funcsetcres2
    wph
    cO
    cS
    cQ
    cE
    yoneda.e
    yoneda.q
    @13
    @17
    evlfcl
    sseldd
    jca
end
