include "wcel.mm"
include "cmgp.mm"
include "cfv.mm"
include "ccnfld.mm"
include "cmhm.mm"
include "co.mm"
include "cdif.mm"
include "cc0.mm"
include "csn.mm"
include "cxp.mm"
include "wss.mm"
include "wa.mm"
include "cv.mm"
include "wne.mm"
include "wi.mm"
include "wral.mm"
include "dchrelbas.mm"
include "cres.mm"
include "wceq.mm"
include "cdm.mm"
include "wfun.mm"
include "cc.mm"
include "wf.mm"
include "eqid.mm"
include "mgpbas.mm"
include "cnfldbas.mm"
include "mhmf.mm"
include "adantl.mm"
include "ffun.mm"
include "syl.mm"
include "funssres.mm"
include "sylan.mm"
include "simpr.mm"
include "resss.mm"
include "syl6eqssr.mm"
include "impbida.mm"
include "0cn.mm"
include "fconst6g.mm"
include "mp1i.mm"
include "fdm.mm"
include "reseq2d.mm"
include "eqeq1d.mm"
include "bitrd.mm"
include "wfn.mm"
include "wb.mm"
include "difss.mm"
include "fssres.mm"
include "sylancl.mm"
include "ffn.mm"
include "eqfnfv.mm"
include "syl2anc.mm"
include "fvres.mm"
include "c0ex.mm"
include "fvconst2.mm"
include "eqeq12d.mm"
include "ralbiia.mm"
include "wn.mm"
include "eldif.mm"
include "imbi1i.mm"
include "impexp.mm"
include "con1b.mm"
include "df-ne.mm"
include "bitr4i.mm"
include "imbi2i.mm"
include "3bitri.mm"
include "ralbii2.mm"
include "bitri.mm"
include "syl6bb.mm"
include "pm5.32da.mm"

theorem dchrelbas2
  let wph: wff ph
  let vx: setvar x
  let cB: class B
  let cD: class D
  let cU: class U
  let cG: class G
  let cN: class N
  let cX: class X
  let cZ: class Z
  let cA: class A
  let vk: setvar k
  let vy: setvar y
  let vz: setvar z
  let vb: setvar b
  let vn: setvar n
  let cC: class C
  let cE: class E
  let cY: class Y
  assume dchrval.g: |- G = ( DChr ` N )
  assume dchrval.z: |- Z = ( Z/nZ ` N )
  assume dchrval.b: |- B = ( Base ` Z )
  assume dchrval.u: |- U = ( Unit ` Z )
  assume dchrval.n: |- ( ph -> N e. NN )
  assume dchrbas.b: |- D = ( Base ` G )

  disjoint B x
  disjoint N x
  disjoint U x
  disjoint ph x
  disjoint X x
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
  disjoint X y
  disjoint X z
  disjoint Z k
  disjoint Z y
  disjoint Z z
  disjoint Y k
  assert |- ( ph -> ( X e. D <-> ( X e. ( ( mulGrp ` Z ) MndHom ( mulGrp ` CCfld ) ) /\ A. x e. B ( ( X ` x ) =/= 0 -> x e. U ) ) ) )

  proof
    wph
    cX
    cD
    wcel
    cX
    cZ
    cmgp
    cfv
    #
    ccnfld
    cmgp
    cfv
    #
    cmhm
    co
    wcel
    #
    cB
    cU
    cdif
    #
    cc0
    csn
    cxp
    #
    cX
    wss
    #
    wa
    @2
    vx
    cv
    #
    cX
    cfv
    #
    cc0
    wne
    #
    @6
    cU
    wcel
    #
    wi
    #
    vx
    cB
    wral
    #
    wa
    wph
    cB
    cD
    cU
    cG
    cN
    cX
    cZ
    dchrval.g
    dchrval.z
    dchrval.b
    dchrval.u
    dchrval.n
    dchrbas.b
    dchrelbas
    wph
    @2
    @5
    @11
    wph
    @2
    wa
    #
    @5
    cX
    @3
    cres
    #
    @4
    wceq
    #
    @11
    @12
    @5
    cX
    @4
    cdm
    #
    cres
    #
    @4
    wceq
    #
    @14
    @12
    @5
    @17
    @12
    cX
    wfun
    #
    @5
    @17
    @12
    cB
    cc
    cX
    wf
    #
    @18
    @2
    @19
    wph
    cB
    cc
    @0
    @1
    cX
    cB
    cZ
    @0
    @0
    eqid
    dchrval.b
    mgpbas
    cc
    ccnfld
    @1
    @1
    eqid
    cnfldbas
    mgpbas
    mhmf
    adantl
    #
    cB
    cc
    cX
    ffun
    syl
    cX
    @4
    funssres
    sylan
    @12
    @17
    wa
    @4
    @16
    cX
    @12
    @17
    simpr
    cX
    @15
    resss
    syl6eqssr
    impbida
    @12
    @16
    @13
    @4
    @12
    @15
    @3
    cX
    @12
    @3
    cc
    @4
    wf
    #
    @15
    @3
    wceq
    cc0
    cc
    wcel
    @21
    @12
    0cn
    @3
    cc0
    cc
    fconst6g
    mp1i
    #
    @3
    cc
    @4
    fdm
    syl
    reseq2d
    eqeq1d
    bitrd
    @12
    @14
    @6
    @13
    cfv
    #
    @6
    @4
    cfv
    #
    wceq
    #
    vx
    @3
    wral
    #
    @11
    @12
    @13
    @3
    wfn
    #
    @4
    @3
    wfn
    #
    @14
    @26
    wb
    @12
    @3
    cc
    @13
    wf
    #
    @27
    @12
    @19
    @3
    cB
    wss
    @29
    @20
    cB
    cU
    difss
    cB
    cc
    @3
    cX
    fssres
    sylancl
    @3
    cc
    @13
    ffn
    syl
    @12
    @21
    @28
    @22
    @3
    cc
    @4
    ffn
    syl
    vx
    @3
    @13
    @4
    eqfnfv
    syl2anc
    @26
    @7
    cc0
    wceq
    #
    vx
    @3
    wral
    @11
    @25
    @30
    vx
    @3
    @6
    @3
    wcel
    #
    @23
    @7
    @24
    cc0
    @6
    @3
    cX
    fvres
    @3
    cc0
    @6
    c0ex
    fvconst2
    eqeq12d
    ralbiia
    @30
    @10
    vx
    @3
    cB
    @31
    @30
    wi
    @6
    cB
    wcel
    #
    @9
    wn
    #
    wa
    #
    @30
    wi
    @32
    @33
    @30
    wi
    #
    wi
    @32
    @10
    wi
    @31
    @34
    @30
    @6
    cB
    cU
    eldif
    imbi1i
    @32
    @33
    @30
    impexp
    @35
    @10
    @32
    @35
    @30
    wn
    #
    @9
    wi
    @10
    @9
    @30
    con1b
    @8
    @36
    @9
    @7
    cc0
    df-ne
    imbi1i
    bitr4i
    imbi2i
    3bitri
    ralbii2
    bitri
    syl6bb
    bitrd
    pm5.32da
    bitrd
end
