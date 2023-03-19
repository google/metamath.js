include "cnv.mm"
include "wcel.mm"
include "w3a.mm"
include "c4.mm"
include "co.mm"
include "cmul.mm"
include "cfv.mm"
include "c2.mm"
include "cexp.mm"
include "c1.mm"
include "cneg.mm"
include "cmin.mm"
include "ci.mm"
include "caddc.mm"
include "cdiv.mm"
include "ipval2.mm"
include "oveq2d.mm"
include "cc.mm"
include "wceq.mm"
include "cr.mm"
include "simp1.mm"
include "nvgcl.mm"
include "nvcl.mm"
include "syl2anc.mm"
include "recnd.mm"
include "sqcld.mm"
include "neg1cn.mm"
include "nvscl.mm"
include "mp3an2.mm"
include "3adant2.mm"
include "syld3an3.mm"
include "subcld.mm"
include "ax-icn.mm"
include "negicn.mm"
include "mulcl.mm"
include "sylancr.mm"
include "addcld.mm"
include "cc0.mm"
include "wne.mm"
include "4cn.mm"
include "4ne0.mm"
include "divcan2.mm"
include "mp3an23.mm"
include "syl.mm"
include "eqtrd.mm"

theorem 4ipval2
  let cA: class A
  let cB: class B
  let cP: class P
  let cS: class S
  let cU: class U
  let cG: class G
  let cN: class N
  let cX: class X
  let vk: setvar k
  let vu: setvar u
  let vx: setvar x
  let vy: setvar y
  assume dipfval.1: |- X = ( BaseSet ` U )
  assume dipfval.2: |- G = ( +v ` U )
  assume dipfval.4: |- S = ( .sOLD ` U )
  assume dipfval.6: |- N = ( normCV ` U )
  assume dipfval.7: |- P = ( .iOLD ` U )


  assert |- ( ( U e. NrmCVec /\ A e. X /\ B e. X ) -> ( 4 x. ( A P B ) ) = ( ( ( ( N ` ( A G B ) ) ^ 2 ) - ( ( N ` ( A G ( -u 1 S B ) ) ) ^ 2 ) ) + ( _i x. ( ( ( N ` ( A G ( _i S B ) ) ) ^ 2 ) - ( ( N ` ( A G ( -u _i S B ) ) ) ^ 2 ) ) ) ) )

  proof
    cU
    cnv
    wcel
    #
    cA
    cX
    wcel
    #
    cB
    cX
    wcel
    #
    w3a
    #
    c4
    cA
    cB
    cP
    co
    #
    cmul
    co
    c4
    cA
    cB
    cG
    co
    #
    cN
    cfv
    #
    c2
    cexp
    co
    #
    cA
    c1
    cneg
    #
    cB
    cS
    co
    #
    cG
    co
    #
    cN
    cfv
    #
    c2
    cexp
    co
    #
    cmin
    co
    #
    ci
    cA
    ci
    cB
    cS
    co
    #
    cG
    co
    #
    cN
    cfv
    #
    c2
    cexp
    co
    #
    cA
    ci
    cneg
    #
    cB
    cS
    co
    #
    cG
    co
    #
    cN
    cfv
    #
    c2
    cexp
    co
    #
    cmin
    co
    #
    cmul
    co
    #
    caddc
    co
    #
    c4
    cdiv
    co
    #
    cmul
    co
    #
    @25
    @3
    @4
    @26
    c4
    cmul
    cA
    cB
    cP
    cS
    cU
    cG
    cN
    cX
    dipfval.1
    dipfval.2
    dipfval.4
    dipfval.6
    dipfval.7
    ipval2
    oveq2d
    @3
    @25
    cc
    wcel
    #
    @27
    @25
    wceq
    #
    @3
    @13
    @24
    @3
    @7
    @12
    @3
    @6
    @3
    @6
    @3
    @0
    @5
    cX
    wcel
    @6
    cr
    wcel
    @0
    @1
    @2
    simp1
    #
    cA
    cB
    cU
    cG
    cX
    dipfval.1
    dipfval.2
    nvgcl
    @5
    cU
    cN
    cX
    dipfval.1
    dipfval.6
    nvcl
    syl2anc
    recnd
    sqcld
    @3
    @11
    @3
    @11
    @3
    @0
    @10
    cX
    wcel
    #
    @11
    cr
    wcel
    @30
    @0
    @1
    @2
    @9
    cX
    wcel
    #
    @31
    @0
    @2
    @32
    @1
    @0
    @8
    cc
    wcel
    @2
    @32
    neg1cn
    @8
    cB
    cS
    cU
    cX
    dipfval.1
    dipfval.4
    nvscl
    mp3an2
    3adant2
    cA
    @9
    cU
    cG
    cX
    dipfval.1
    dipfval.2
    nvgcl
    syld3an3
    @10
    cU
    cN
    cX
    dipfval.1
    dipfval.6
    nvcl
    syl2anc
    recnd
    sqcld
    subcld
    @3
    ci
    cc
    wcel
    #
    @23
    cc
    wcel
    @24
    cc
    wcel
    ax-icn
    @3
    @17
    @22
    @3
    @16
    @3
    @16
    @3
    @0
    @15
    cX
    wcel
    #
    @16
    cr
    wcel
    @30
    @0
    @1
    @2
    @14
    cX
    wcel
    #
    @34
    @0
    @2
    @35
    @1
    @0
    @33
    @2
    @35
    ax-icn
    ci
    cB
    cS
    cU
    cX
    dipfval.1
    dipfval.4
    nvscl
    mp3an2
    3adant2
    cA
    @14
    cU
    cG
    cX
    dipfval.1
    dipfval.2
    nvgcl
    syld3an3
    @15
    cU
    cN
    cX
    dipfval.1
    dipfval.6
    nvcl
    syl2anc
    recnd
    sqcld
    @3
    @21
    @3
    @21
    @3
    @0
    @20
    cX
    wcel
    #
    @21
    cr
    wcel
    @30
    @0
    @1
    @2
    @19
    cX
    wcel
    #
    @36
    @0
    @2
    @37
    @1
    @0
    @18
    cc
    wcel
    @2
    @37
    negicn
    @18
    cB
    cS
    cU
    cX
    dipfval.1
    dipfval.4
    nvscl
    mp3an2
    3adant2
    cA
    @19
    cU
    cG
    cX
    dipfval.1
    dipfval.2
    nvgcl
    syld3an3
    @20
    cU
    cN
    cX
    dipfval.1
    dipfval.6
    nvcl
    syl2anc
    recnd
    sqcld
    subcld
    ci
    @23
    mulcl
    sylancr
    addcld
    @28
    c4
    cc
    wcel
    c4
    cc0
    wne
    @29
    4cn
    4ne0
    @25
    c4
    divcan2
    mp3an23
    syl
    eqtrd
end
