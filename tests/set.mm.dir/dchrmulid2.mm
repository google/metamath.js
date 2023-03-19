include "co.mm"
include "cmul.mm"
include "cof.mm"
include "wcel.mm"
include "cn.mm"
include "dchrrcl.mm"
include "syl.mm"
include "dchr1cl.mm"
include "dchrmul.mm"
include "cv.mm"
include "c1.mm"
include "cc0.mm"
include "cif.mm"
include "cfv.mm"
include "cmpt.mm"
include "wceq.mm"
include "wa.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "cc.mm"
include "dchrf.mm"
include "ffvelrnda.mm"
include "adantr.mm"
include "mulid2d.mm"
include "wn.mm"
include "0cn.mm"
include "mul02i.mm"
include "wne.mm"
include "wi.mm"
include "cmgp.mm"
include "ccnfld.mm"
include "cmhm.mm"
include "wral.mm"
include "dchrelbas2.mm"
include "mpbid.mm"
include "simprd.mm"
include "r19.21bi.mm"
include "necon1bd.mm"
include "imp.mm"
include "oveq2d.mm"
include "3eqtr4a.mm"
include "ifbothda.mm"
include "mpteq2dva.mm"
include "cvv.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "a1i.mm"
include "ax-1cn.mm"
include "keepel.mm"
include "feqmptd.mm"
include "offval2.mm"
include "3eqtr4d.mm"
include "eqtrd.mm"

theorem dchrmulid2
  let wph: wff ph
  let cB: class B
  let cD: class D
  let c.x: class .x.
  let cU: class U
  let c.1: class .1.
  let vk: setvar k
  let cG: class G
  let cN: class N
  let cX: class X
  let cZ: class Z
  let vx: setvar x
  let vy: setvar y
  let cK: class K
  let cL: class L
  let cA: class A
  let cY: class Y
  assume dchrmhm.g: |- G = ( DChr ` N )
  assume dchrmhm.z: |- Z = ( Z/nZ ` N )
  assume dchrmhm.b: |- D = ( Base ` G )
  assume dchrn0.b: |- B = ( Base ` Z )
  assume dchrn0.u: |- U = ( Unit ` Z )
  assume dchr1cl.o: |- .1. = ( k e. B |-> if ( k e. U , 1 , 0 ) )
  assume dchrmulid2.t: |- .x. = ( +g ` G )
  assume dchrmulid2.x: |- ( ph -> X e. D )

  disjoint B k
  disjoint U k
  disjoint N k
  disjoint k ph
  disjoint X k
  disjoint Z k
  disjoint x y
  disjoint .1. x
  disjoint .1. y
  disjoint k x
  disjoint k y
  disjoint B x
  disjoint B y
  disjoint K x
  disjoint K y
  disjoint L x
  disjoint L y
  disjoint U x
  disjoint U y
  disjoint A x
  disjoint N x
  disjoint N y
  disjoint ph x
  disjoint ph y
  disjoint X x
  disjoint X y
  disjoint Z x
  disjoint Z y
  disjoint D x
  disjoint Y x
  disjoint Y y
  assert |- ( ph -> ( .1. .x. X ) = X )

  proof
    wph
    c.1
    cX
    c.x
    co
    c.1
    cX
    cmul
    cof
    co
    #
    cX
    wph
    cD
    c.x
    cG
    cN
    c.1
    cX
    cZ
    dchrmhm.g
    dchrmhm.z
    dchrmhm.b
    dchrmulid2.t
    wph
    cB
    cD
    cU
    c.1
    vk
    cG
    cN
    cZ
    dchrmhm.g
    dchrmhm.z
    dchrmhm.b
    dchrn0.b
    dchrn0.u
    dchr1cl.o
    wph
    cX
    cD
    wcel
    #
    cN
    cn
    wcel
    dchrmulid2.x
    cD
    cG
    cN
    cX
    dchrmhm.g
    dchrmhm.b
    dchrrcl
    syl
    #
    dchr1cl
    dchrmulid2.x
    dchrmul
    wph
    vk
    cB
    vk
    cv
    #
    cU
    wcel
    #
    c1
    cc0
    cif
    #
    @3
    cX
    cfv
    #
    cmul
    co
    #
    cmpt
    vk
    cB
    @6
    cmpt
    @0
    cX
    wph
    vk
    cB
    @7
    @6
    @4
    c1
    @6
    cmul
    co
    #
    @6
    wceq
    cc0
    @6
    cmul
    co
    #
    @6
    wceq
    @7
    @6
    wceq
    wph
    @3
    cB
    wcel
    wa
    #
    c1
    cc0
    c1
    @5
    wceq
    @8
    @7
    @6
    c1
    @5
    @6
    cmul
    oveq1
    eqeq1d
    cc0
    @5
    wceq
    @9
    @7
    @6
    cc0
    @5
    @6
    cmul
    oveq1
    eqeq1d
    @10
    @4
    wa
    @6
    @10
    @6
    cc
    wcel
    @4
    wph
    cB
    cc
    @3
    cX
    wph
    cB
    cD
    cG
    cN
    cX
    cZ
    dchrmhm.g
    dchrmhm.z
    dchrmhm.b
    dchrn0.b
    dchrmulid2.x
    dchrf
    #
    ffvelrnda
    #
    adantr
    mulid2d
    @10
    @4
    wn
    #
    wa
    #
    cc0
    cc0
    cmul
    co
    cc0
    @9
    @6
    cc0
    0cn
    mul02i
    @14
    @6
    cc0
    cc0
    cmul
    @10
    @13
    @6
    cc0
    wceq
    @10
    @4
    @6
    cc0
    wph
    @6
    cc0
    wne
    @4
    wi
    #
    vk
    cB
    wph
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
    @15
    vk
    cB
    wral
    #
    wph
    @1
    @16
    @17
    wa
    dchrmulid2.x
    wph
    vk
    cB
    cD
    cU
    cG
    cN
    cX
    cZ
    dchrmhm.g
    dchrmhm.z
    dchrn0.b
    dchrn0.u
    @2
    dchrmhm.b
    dchrelbas2
    mpbid
    simprd
    r19.21bi
    necon1bd
    imp
    #
    oveq2d
    @18
    3eqtr4a
    ifbothda
    mpteq2dva
    wph
    vk
    cB
    @5
    @6
    cmul
    c.1
    cX
    cvv
    cc
    cc
    cB
    cvv
    wcel
    wph
    cB
    cZ
    cbs
    cfv
    cvv
    dchrn0.b
    cZ
    cbs
    fvex
    eqeltri
    a1i
    @5
    cc
    wcel
    @10
    @4
    c1
    cc0
    cc
    ax-1cn
    0cn
    keepel
    a1i
    @12
    c.1
    vk
    cB
    @5
    cmpt
    wceq
    wph
    dchr1cl.o
    a1i
    wph
    vk
    cB
    cc
    cX
    @11
    feqmptd
    #
    offval2
    @19
    3eqtr4d
    eqtrd
end
