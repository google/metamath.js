include "wcel.mm"
include "cn.mm"
include "cmgp.mm"
include "cfv.mm"
include "ccnfld.mm"
include "cmhm.mm"
include "co.mm"
include "c1.mm"
include "cv.mm"
include "cgcd.mm"
include "clt.mm"
include "wbr.mm"
include "cc0.mm"
include "wceq.mm"
include "wi.mm"
include "cz.mm"
include "wral.mm"
include "wa.mm"
include "w3a.mm"
include "dchrrcl.mm"
include "wne.mm"
include "cui.mm"
include "cbs.mm"
include "eqid.mm"
include "id.mm"
include "dchrelbas2.mm"
include "cn0.mm"
include "wfo.mm"
include "wb.mm"
include "nnnn0.mm"
include "adantr.mm"
include "znzrhfo.mm"
include "fveq2.mm"
include "neeq1d.mm"
include "eleq1.mm"
include "imbi12d.mm"
include "cbvfo.mm"
include "3syl.mm"
include "wn.mm"
include "df-ne.mm"
include "a1i.mm"
include "znunit.mm"
include "sylan.mm"
include "1red.mm"
include "simpr.mm"
include "simpll.mm"
include "nnzd.mm"
include "nnne0.mm"
include "necon3ai.mm"
include "gcdn0cl.mm"
include "syl21anc.mm"
include "nnred.mm"
include "nnge1d.mm"
include "leltned.mm"
include "necon2bbid.mm"
include "bitrd.mm"
include "con34b.mm"
include "syl6bbr.mm"
include "ralbidva.mm"
include "bitr3d.mm"
include "pm5.32da.mm"
include "biadan2.mm"
include "3anass.mm"
include "bitr4i.mm"

theorem dchrelbas4
  let vx: setvar x
  let cD: class D
  let cG: class G
  let cL: class L
  let cN: class N
  let cX: class X
  let cZ: class Z
  let vy: setvar y
  let c.1: class .1.
  let vk: setvar k
  let cB: class B
  let cK: class K
  let cU: class U
  let cA: class A
  let wph: wff ph
  let cY: class Y
  assume dchrmhm.g: |- G = ( DChr ` N )
  assume dchrmhm.z: |- Z = ( Z/nZ ` N )
  assume dchrmhm.b: |- D = ( Base ` G )
  assume dchrelbas4.l: |- L = ( ZRHom ` Z )

  disjoint L x
  disjoint N x
  disjoint X x
  disjoint Z x
  disjoint D x
  disjoint x y
  disjoint .1. x
  disjoint .1. y
  disjoint k x
  disjoint k y
  disjoint B k
  disjoint B x
  disjoint B y
  disjoint K x
  disjoint K y
  disjoint L y
  disjoint U k
  disjoint U x
  disjoint U y
  disjoint A x
  disjoint N k
  disjoint N y
  disjoint k ph
  disjoint ph x
  disjoint ph y
  disjoint X k
  disjoint X y
  disjoint Z k
  disjoint Z y
  disjoint Y x
  disjoint Y y
  assert |- ( X e. D <-> ( N e. NN /\ X e. ( ( mulGrp ` Z ) MndHom ( mulGrp ` CCfld ) ) /\ A. x e. ZZ ( 1 < ( x gcd N ) -> ( X ` ( L ` x ) ) = 0 ) ) )

  proof
    cX
    cD
    wcel
    #
    cN
    cn
    wcel
    #
    cX
    cZ
    cmgp
    cfv
    ccnfld
    cmgp
    cfv
    cmhm
    co
    wcel
    #
    c1
    vx
    cv
    #
    cN
    cgcd
    co
    #
    clt
    wbr
    #
    @3
    cL
    cfv
    #
    cX
    cfv
    #
    cc0
    wceq
    #
    wi
    #
    vx
    cz
    wral
    #
    wa
    #
    wa
    @1
    @2
    @10
    w3a
    @0
    @1
    @11
    cD
    cG
    cN
    cX
    dchrmhm.g
    dchrmhm.b
    dchrrcl
    @1
    @0
    @2
    vy
    cv
    #
    cX
    cfv
    #
    cc0
    wne
    #
    @12
    cZ
    cui
    cfv
    #
    wcel
    #
    wi
    #
    vy
    cZ
    cbs
    cfv
    #
    wral
    #
    wa
    @11
    @1
    vy
    @18
    cD
    @15
    cG
    cN
    cX
    cZ
    dchrmhm.g
    dchrmhm.z
    @18
    eqid
    #
    @15
    eqid
    #
    @1
    id
    dchrmhm.b
    dchrelbas2
    @1
    @2
    @19
    @10
    @1
    @2
    wa
    #
    @7
    cc0
    wne
    #
    @6
    @15
    wcel
    #
    wi
    #
    vx
    cz
    wral
    #
    @19
    @10
    @22
    cN
    cn0
    wcel
    #
    cz
    @18
    cL
    wfo
    @26
    @19
    wb
    @1
    @27
    @2
    cN
    nnnn0
    adantr
    #
    @18
    cL
    cN
    cZ
    dchrmhm.z
    @20
    dchrelbas4.l
    znzrhfo
    @25
    @17
    vx
    vy
    cz
    @18
    cL
    @6
    @12
    wceq
    #
    @23
    @14
    @24
    @16
    @29
    @7
    @13
    cc0
    @6
    @12
    cX
    fveq2
    neeq1d
    @6
    @12
    @15
    eleq1
    imbi12d
    cbvfo
    3syl
    @22
    @25
    @9
    vx
    cz
    @22
    @3
    cz
    wcel
    #
    wa
    #
    @25
    @8
    wn
    #
    @5
    wn
    #
    wi
    @9
    @31
    @23
    @32
    @24
    @33
    @23
    @32
    wb
    @31
    @7
    cc0
    df-ne
    a1i
    @31
    @24
    @4
    c1
    wceq
    #
    @33
    @22
    @27
    @30
    @24
    @34
    wb
    @28
    @3
    @15
    cL
    cN
    cZ
    dchrmhm.z
    @21
    dchrelbas4.l
    znunit
    sylan
    @31
    @5
    @4
    c1
    @31
    c1
    @4
    @31
    1red
    @31
    @4
    @31
    @30
    cN
    cz
    wcel
    @3
    cc0
    wceq
    #
    cN
    cc0
    wceq
    #
    wa
    #
    wn
    #
    @4
    cn
    wcel
    @22
    @30
    simpr
    @31
    cN
    @1
    @2
    @30
    simpll
    #
    nnzd
    @31
    @1
    cN
    cc0
    wne
    @38
    @39
    cN
    nnne0
    @37
    cN
    cc0
    @35
    @36
    simpr
    necon3ai
    3syl
    @3
    cN
    gcdn0cl
    syl21anc
    #
    nnred
    @31
    @4
    @40
    nnge1d
    leltned
    necon2bbid
    bitrd
    imbi12d
    @5
    @8
    con34b
    syl6bbr
    ralbidva
    bitr3d
    pm5.32da
    bitrd
    biadan2
    @1
    @2
    @10
    3anass
    bitr4i
end
