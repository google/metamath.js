include "cn.mm"
include "wcel.mm"
include "cc.mm"
include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cbp.mm"
include "cmin.mm"
include "cexp.mm"
include "cmul.mm"
include "wceq.mm"
include "cv.mm"
include "wi.mm"
include "oveq1.mm"
include "oveq12d.mm"
include "id.mm"
include "oveq2d.mm"
include "eqeq12d.mm"
include "imbi2d.mm"
include "cfz.mm"
include "wral.mm"
include "w3a.mm"
include "simp1.mm"
include "simp3.mm"
include "wa.mm"
include "simpl3.mm"
include "rspccva.mm"
include "3ad2antl2.mm"
include "mpd.mm"
include "bpolydiflem.mm"
include "3exp.mm"
include "nnsinds.mm"
include "imp.mm"

theorem bpolydif
  let cN: class N
  let cX: class X
  let vk: setvar k
  let vm: setvar m
  let vn: setvar n
  let wph: wff ph


  assert |- ( ( N e. NN /\ X e. CC ) -> ( ( N BernPoly ( X + 1 ) ) - ( N BernPoly X ) ) = ( N x. ( X ^ ( N - 1 ) ) ) )

  proof
    cN
    cn
    wcel
    cX
    cc
    wcel
    #
    cN
    cX
    c1
    caddc
    co
    #
    cbp
    co
    #
    cN
    cX
    cbp
    co
    #
    cmin
    co
    #
    cN
    cX
    cN
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
    wceq
    #
    @0
    vn
    cv
    #
    @1
    cbp
    co
    #
    @9
    cX
    cbp
    co
    #
    cmin
    co
    #
    @9
    cX
    @9
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
    wceq
    #
    wi
    @0
    vk
    cv
    #
    @1
    cbp
    co
    #
    @17
    cX
    cbp
    co
    #
    cmin
    co
    #
    @17
    cX
    @17
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
    wceq
    #
    wi
    #
    @0
    @8
    wi
    vn
    vk
    cN
    @9
    @17
    wceq
    #
    @16
    @24
    @0
    @26
    @12
    @20
    @15
    @23
    @26
    @10
    @18
    @11
    @19
    cmin
    @9
    @17
    @1
    cbp
    oveq1
    @9
    @17
    cX
    cbp
    oveq1
    oveq12d
    @26
    @9
    @17
    @14
    @22
    cmul
    @26
    id
    @26
    @13
    @21
    cX
    cexp
    @9
    @17
    c1
    cmin
    oveq1
    oveq2d
    oveq12d
    eqeq12d
    imbi2d
    @9
    cN
    wceq
    #
    @16
    @8
    @0
    @27
    @12
    @4
    @15
    @7
    @27
    @10
    @2
    @11
    @3
    cmin
    @9
    cN
    @1
    cbp
    oveq1
    @9
    cN
    cX
    cbp
    oveq1
    oveq12d
    @27
    @9
    cN
    @14
    @6
    cmul
    @27
    id
    @27
    @13
    @5
    cX
    cexp
    @9
    cN
    c1
    cmin
    oveq1
    oveq2d
    oveq12d
    eqeq12d
    imbi2d
    @9
    cn
    wcel
    #
    @25
    vk
    c1
    @13
    cfz
    co
    #
    wral
    #
    @0
    @16
    @28
    @30
    @0
    w3a
    #
    vm
    @9
    cX
    @28
    @30
    @0
    simp1
    @28
    @30
    @0
    simp3
    @31
    vm
    cv
    #
    @29
    wcel
    #
    wa
    @0
    @32
    @1
    cbp
    co
    #
    @32
    cX
    cbp
    co
    #
    cmin
    co
    #
    @32
    cX
    @32
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
    wceq
    #
    @28
    @30
    @0
    @33
    simpl3
    @30
    @28
    @33
    @0
    @40
    wi
    #
    @0
    @25
    @41
    vk
    @32
    @29
    @17
    @32
    wceq
    #
    @24
    @40
    @0
    @42
    @20
    @36
    @23
    @39
    @42
    @18
    @34
    @19
    @35
    cmin
    @17
    @32
    @1
    cbp
    oveq1
    @17
    @32
    cX
    cbp
    oveq1
    oveq12d
    @42
    @17
    @32
    @22
    @38
    cmul
    @42
    id
    @42
    @21
    @37
    cX
    cexp
    @17
    @32
    c1
    cmin
    oveq1
    oveq2d
    oveq12d
    eqeq12d
    imbi2d
    rspccva
    3ad2antl2
    mpd
    bpolydiflem
    3exp
    nnsinds
    imp
end
