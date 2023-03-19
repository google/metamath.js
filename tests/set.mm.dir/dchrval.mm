include "cdchr.mm"
include "cfv.mm"
include "cnx.mm"
include "cbs.mm"
include "cop.mm"
include "cplusg.mm"
include "cmul.mm"
include "cof.mm"
include "cxp.mm"
include "cres.mm"
include "cpr.mm"
include "cv.mm"
include "czn.mm"
include "cui.mm"
include "cdif.mm"
include "cc0.mm"
include "csn.mm"
include "wss.mm"
include "cmgp.mm"
include "ccnfld.mm"
include "cmhm.mm"
include "co.mm"
include "crab.mm"
include "csb.mm"
include "cn.mm"
include "cvv.mm"
include "cmpt.mm"
include "wceq.mm"
include "df-dchr.mm"
include "a1i.mm"
include "wa.mm"
include "fvexd.mm"
include "wcel.mm"
include "ovex.mm"
include "rabex.mm"
include "ad2antrr.mm"
include "simpr.mm"
include "fveq2d.mm"
include "syl6reqr.mm"
include "eqeq2d.mm"
include "biimpar.mm"
include "oveq1d.mm"
include "syl6eqr.mm"
include "difeq12d.mm"
include "xpeq1d.mm"
include "sseq1d.mm"
include "rabeqbidv.mm"
include "eqtr4d.mm"
include "opeq2d.mm"
include "sqxpeqd.mm"
include "reseq2d.mm"
include "preq12d.mm"
include "csbied.mm"
include "prex.mm"
include "fvmptd.mm"
include "syl5eq.mm"

theorem dchrval
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let cD: class D
  let cU: class U
  let cG: class G
  let cN: class N
  let cZ: class Z
  let cA: class A
  let vk: setvar k
  let vy: setvar y
  let vz: setvar z
  let vb: setvar b
  let vn: setvar n
  let cC: class C
  let cE: class E
  let cX: class X
  let cY: class Y
  assume dchrval.g: |- G = ( DChr ` N )
  assume dchrval.z: |- Z = ( Z/nZ ` N )
  assume dchrval.b: |- B = ( Base ` Z )
  assume dchrval.u: |- U = ( Unit ` Z )
  assume dchrval.n: |- ( ph -> N e. NN )
  assume dchrval.d: |- ( ph -> D = { x e. ( ( mulGrp ` Z ) MndHom ( mulGrp ` CCfld ) ) | ( ( B \ U ) X. { 0 } ) C_ x } )

  disjoint B x
  disjoint N x
  disjoint U x
  disjoint ph x
  disjoint Z x
  disjoint A k
  disjoint k x
  disjoint k y
  disjoint k z
  disjoint B k
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B y
  disjoint B z
  disjoint b n
  disjoint b z
  disjoint D b
  disjoint n z
  disjoint D n
  disjoint D z
  disjoint b x
  disjoint N b
  disjoint n x
  disjoint N n
  disjoint N z
  disjoint U k
  disjoint U y
  disjoint U z
  disjoint C k
  disjoint E k
  disjoint b k
  disjoint b y
  disjoint b ph
  disjoint k n
  disjoint k ph
  disjoint n y
  disjoint n ph
  disjoint ph y
  disjoint ph z
  disjoint X x
  disjoint X y
  disjoint X z
  disjoint Z k
  disjoint Z y
  disjoint Z z
  disjoint Y k
  assert |- ( ph -> G = { <. ( Base ` ndx ) , D >. , <. ( +g ` ndx ) , ( oF x. |` ( D X. D ) ) >. } )

  proof
    wph
    cG
    cN
    cdchr
    cfv
    cnx
    cbs
    cfv
    #
    cD
    cop
    #
    cnx
    cplusg
    cfv
    #
    cmul
    cof
    #
    cD
    cD
    cxp
    #
    cres
    #
    cop
    #
    cpr
    #
    dchrval.g
    wph
    vn
    cN
    vz
    vn
    cv
    #
    czn
    cfv
    #
    vb
    vz
    cv
    #
    cbs
    cfv
    #
    @10
    cui
    cfv
    #
    cdif
    #
    cc0
    csn
    #
    cxp
    #
    vx
    cv
    #
    wss
    #
    vx
    @10
    cmgp
    cfv
    #
    ccnfld
    cmgp
    cfv
    #
    cmhm
    co
    #
    crab
    #
    @0
    vb
    cv
    #
    cop
    #
    @2
    @3
    @22
    @22
    cxp
    #
    cres
    #
    cop
    #
    cpr
    #
    csb
    #
    csb
    #
    @7
    cn
    cdchr
    cvv
    cdchr
    vn
    cn
    @29
    cmpt
    wceq
    wph
    vx
    vz
    vn
    vb
    df-dchr
    a1i
    wph
    @8
    cN
    wceq
    #
    wa
    #
    vz
    @9
    @28
    @7
    cvv
    @31
    @8
    czn
    fvexd
    @31
    @10
    @9
    wceq
    #
    wa
    #
    vb
    @21
    @27
    @7
    cvv
    @21
    cvv
    wcel
    @33
    @17
    vx
    @20
    @18
    @19
    cmhm
    ovex
    rabex
    a1i
    @33
    @22
    @21
    wceq
    #
    wa
    #
    @23
    @1
    @26
    @6
    @35
    @22
    cD
    @0
    @33
    @22
    cD
    wceq
    @34
    @33
    cD
    @21
    @22
    @33
    cD
    cB
    cU
    cdif
    #
    @14
    cxp
    #
    @16
    wss
    #
    vx
    cZ
    cmgp
    cfv
    #
    @19
    cmhm
    co
    #
    crab
    #
    @21
    wph
    cD
    @41
    wceq
    @30
    @32
    dchrval.d
    ad2antrr
    @33
    @17
    @38
    vx
    @20
    @40
    @33
    @18
    @39
    @19
    cmhm
    @33
    @10
    cZ
    cmgp
    @31
    @10
    cZ
    wceq
    @32
    @31
    cZ
    @9
    @10
    @31
    @9
    cN
    czn
    cfv
    cZ
    @31
    @8
    cN
    czn
    wph
    @30
    simpr
    fveq2d
    dchrval.z
    syl6reqr
    eqeq2d
    biimpar
    #
    fveq2d
    oveq1d
    @33
    @15
    @37
    @16
    @33
    @13
    @36
    @14
    @33
    @11
    cB
    @12
    cU
    @33
    @11
    cZ
    cbs
    cfv
    cB
    @33
    @10
    cZ
    cbs
    @42
    fveq2d
    dchrval.b
    syl6eqr
    @33
    @12
    cZ
    cui
    cfv
    cU
    @33
    @10
    cZ
    cui
    @42
    fveq2d
    dchrval.u
    syl6eqr
    difeq12d
    xpeq1d
    sseq1d
    rabeqbidv
    eqtr4d
    eqeq2d
    biimpar
    #
    opeq2d
    @35
    @25
    @5
    @2
    @35
    @24
    @4
    @3
    @35
    @22
    cD
    @43
    sqxpeqd
    reseq2d
    opeq2d
    preq12d
    csbied
    csbied
    dchrval.n
    @7
    cvv
    wcel
    wph
    @1
    @6
    prex
    a1i
    fvmptd
    syl5eq
end
