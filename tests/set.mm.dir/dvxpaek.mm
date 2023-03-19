include "cv.mm"
include "caddc.mm"
include "co.mm"
include "cexp.mm"
include "cmpt.mm"
include "cdv.mm"
include "c1.mm"
include "cmin.mm"
include "cmul.mm"
include "cc0.mm"
include "cc.mm"
include "cr.mm"
include "cpr.mm"
include "wcel.mm"
include "cnelprrecn.mm"
include "a1i.mm"
include "wa.mm"
include "wss.mm"
include "dvdmsscn.mm"
include "adantr.mm"
include "simpr.mm"
include "sseldd.mm"
include "addcld.mm"
include "1red.mm"
include "0red.mm"
include "readdcld.mm"
include "cn0.mm"
include "nnnn0d.mm"
include "expcld.mm"
include "nn0cnd.mm"
include "cn.mm"
include "nnm1nn0.mm"
include "syl.mm"
include "mulcld.mm"
include "dvmptidg.mm"
include "dvmptconst.mm"
include "dvmptadd.mm"
include "wceq.mm"
include "dvexp.mm"
include "oveq1.mm"
include "oveq2d.mm"
include "dvmptco.mm"
include "1p0e1.mm"
include "oveq2i.mm"
include "nncnd.mm"
include "mulid1d.mm"
include "eqtrd.mm"
include "mpteq2dva.mm"

theorem dvxpaek
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cS: class S
  let cK: class K
  let cX: class X
  let vy: setvar y
  let vk: setvar k
  assume dvxpaek.s: |- ( ph -> S e. { RR , CC } )
  assume dvxpaek.x: |- ( ph -> X e. ( ( TopOpen ` CCfld ) |`t S ) )
  assume dvxpaek.a: |- ( ph -> A e. CC )
  assume dvxpaek.k: |- ( ph -> K e. NN )

  disjoint A x
  disjoint K x
  disjoint S x
  disjoint X x
  disjoint ph x
  disjoint A y
  disjoint x y
  disjoint K y
  disjoint ph y
  disjoint k x
  assert |- ( ph -> ( S _D ( x e. X |-> ( ( x + A ) ^ K ) ) ) = ( x e. X |-> ( K x. ( ( x + A ) ^ ( K - 1 ) ) ) ) )

  proof
    wph
    cS
    vx
    cX
    vx
    cv
    #
    cA
    caddc
    co
    #
    cK
    cexp
    co
    #
    cmpt
    cdv
    co
    vx
    cX
    cK
    @1
    cK
    c1
    cmin
    co
    #
    cexp
    co
    #
    cmul
    co
    #
    c1
    cc0
    caddc
    co
    #
    cmul
    co
    #
    cmpt
    vx
    cX
    @5
    cmpt
    wph
    vx
    vy
    @1
    @6
    vy
    cv
    #
    cK
    cexp
    co
    #
    cK
    @8
    @3
    cexp
    co
    #
    cmul
    co
    #
    cS
    cc
    @2
    @5
    cr
    cc
    cX
    cc
    dvxpaek.s
    cc
    cr
    cc
    cpr
    wcel
    wph
    cnelprrecn
    a1i
    wph
    @0
    cX
    wcel
    #
    wa
    #
    @0
    cA
    @13
    cX
    cc
    @0
    wph
    cX
    cc
    wss
    @12
    wph
    cS
    cX
    dvxpaek.s
    dvxpaek.x
    dvdmsscn
    adantr
    wph
    @12
    simpr
    sseldd
    #
    wph
    cA
    cc
    wcel
    @12
    dvxpaek.a
    adantr
    #
    addcld
    #
    @13
    c1
    cc0
    @13
    1red
    #
    @13
    0red
    #
    readdcld
    wph
    @8
    cc
    wcel
    #
    wa
    #
    @8
    cK
    wph
    @19
    simpr
    #
    wph
    cK
    cn0
    wcel
    @19
    wph
    cK
    dvxpaek.k
    nnnn0d
    adantr
    #
    expcld
    @20
    cK
    @10
    @20
    cK
    @22
    nn0cnd
    @20
    @8
    @3
    @21
    wph
    @3
    cn0
    wcel
    #
    @19
    wph
    cK
    cn
    wcel
    #
    @23
    dvxpaek.k
    cK
    nnm1nn0
    syl
    #
    adantr
    expcld
    mulcld
    wph
    vx
    @0
    c1
    cA
    cc0
    cS
    cr
    cr
    cX
    dvxpaek.s
    @14
    @17
    wph
    vx
    cX
    cS
    dvxpaek.s
    dvxpaek.x
    dvmptidg
    @15
    @18
    wph
    vx
    cX
    cA
    cS
    dvxpaek.s
    dvxpaek.x
    dvxpaek.a
    dvmptconst
    dvmptadd
    wph
    @24
    cc
    vy
    cc
    @9
    cmpt
    cdv
    co
    vy
    cc
    @11
    cmpt
    wceq
    dvxpaek.k
    vy
    cK
    dvexp
    syl
    @8
    @1
    cK
    cexp
    oveq1
    @8
    @1
    wceq
    @10
    @4
    cK
    cmul
    @8
    @1
    @3
    cexp
    oveq1
    oveq2d
    dvmptco
    wph
    vx
    cX
    @7
    @5
    @13
    @7
    @5
    c1
    cmul
    co
    #
    @5
    @7
    @26
    wceq
    @13
    @6
    c1
    @5
    cmul
    1p0e1
    oveq2i
    a1i
    @13
    @5
    @13
    cK
    @4
    wph
    cK
    cc
    wcel
    @12
    wph
    cK
    dvxpaek.k
    nncnd
    adantr
    @13
    @1
    @3
    @16
    wph
    @23
    @12
    @25
    adantr
    expcld
    mulcld
    mulid1d
    eqtrd
    mpteq2dva
    eqtrd
end
