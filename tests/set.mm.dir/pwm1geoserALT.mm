include "cexp.mm"
include "co.mm"
include "c1.mm"
include "cmin.mm"
include "cc0.mm"
include "cfzo.mm"
include "cv.mm"
include "cmul.mm"
include "csu.mm"
include "cfz.mm"
include "cz.mm"
include "wcel.mm"
include "wceq.mm"
include "nn0zd.mm"
include "1exp.mm"
include "syl.mm"
include "eqcomd.mm"
include "oveq2d.mm"
include "cn0.mm"
include "cc.mm"
include "1cnd.mm"
include "pwdif.mm"
include "syl3anc.mm"
include "fzoval.mm"
include "wa.mm"
include "adantr.mm"
include "elfzoelz.mm"
include "adantl.mm"
include "zsubcld.mm"
include "peano2zm.mm"
include "3syl.mm"
include "elfzonn0.mm"
include "expcld.mm"
include "mulid1d.mm"
include "eqtrd.mm"
include "sumeq12dv.mm"
include "3eqtrd.mm"

theorem pwm1geoserALT
  let wph: wff ph
  let cA: class A
  let vk: setvar k
  let cN: class N
  let vx: setvar x
  assume pwm1geoserALT.a: |- ( ph -> A e. CC )
  assume pwm1geoserALT.n: |- ( ph -> N e. NN0 )

  disjoint A k
  disjoint N k
  disjoint k ph
  disjoint k x
  assert |- ( ph -> ( ( A ^ N ) - 1 ) = ( ( A - 1 ) x. sum_ k e. ( 0 ... ( N - 1 ) ) ( A ^ k ) ) )

  proof
    wph
    cA
    cN
    cexp
    co
    #
    c1
    cmin
    co
    @0
    c1
    cN
    cexp
    co
    #
    cmin
    co
    #
    cA
    c1
    cmin
    co
    #
    cc0
    cN
    cfzo
    co
    #
    cA
    vk
    cv
    #
    cexp
    co
    #
    c1
    cN
    @5
    cmin
    co
    #
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
    vk
    csu
    #
    cmul
    co
    #
    @3
    cc0
    cN
    c1
    cmin
    co
    cfz
    co
    #
    @6
    vk
    csu
    #
    cmul
    co
    wph
    c1
    @1
    @0
    cmin
    wph
    @1
    c1
    wph
    cN
    cz
    wcel
    #
    @1
    c1
    wceq
    wph
    cN
    pwm1geoserALT.n
    nn0zd
    #
    cN
    1exp
    syl
    eqcomd
    oveq2d
    wph
    cN
    cn0
    wcel
    cA
    cc
    wcel
    #
    c1
    cc
    wcel
    @2
    @12
    wceq
    pwm1geoserALT.n
    pwm1geoserALT.a
    wph
    1cnd
    cA
    c1
    vk
    cN
    pwdif
    syl3anc
    wph
    @11
    @14
    @3
    cmul
    wph
    @4
    @13
    @10
    @6
    vk
    wph
    @15
    @4
    @13
    wceq
    @16
    cc0
    cN
    fzoval
    syl
    wph
    @5
    @4
    wcel
    #
    wa
    #
    @10
    @6
    c1
    cmul
    co
    @6
    @19
    @9
    c1
    @6
    cmul
    @19
    @7
    cz
    wcel
    @8
    cz
    wcel
    @9
    c1
    wceq
    @19
    cN
    @5
    wph
    @15
    @18
    @16
    adantr
    @18
    @5
    cz
    wcel
    wph
    @5
    cc0
    cN
    elfzoelz
    adantl
    zsubcld
    @7
    peano2zm
    @8
    1exp
    3syl
    oveq2d
    @19
    @6
    @19
    cA
    @5
    wph
    @17
    @18
    pwm1geoserALT.a
    adantr
    @18
    @5
    cn0
    wcel
    wph
    @5
    cN
    elfzonn0
    adantl
    expcld
    mulid1d
    eqtrd
    sumeq12dv
    oveq2d
    3eqtrd
end
