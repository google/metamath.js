include "cv.mm"
include "csin.mm"
include "cfv.mm"
include "ccos.mm"
include "cexp.mm"
include "co.mm"
include "c1.mm"
include "cmin.mm"
include "cmul.mm"
include "cc.mm"
include "cr.mm"
include "cpr.mm"
include "wcel.mm"
include "cnelprrecn.mm"
include "a1i.mm"
include "wf.mm"
include "sinf.mm"
include "ffvelrnda.mm"
include "cosf.mm"
include "wa.mm"
include "simpr.mm"
include "cn0.mm"
include "nnnn0d.mm"
include "adantr.mm"
include "expcld.mm"
include "nncnd.mm"
include "cn.mm"
include "nnm1nn0.mm"
include "syl.mm"
include "mulcld.mm"
include "cdv.mm"
include "cmpt.mm"
include "dvsin.mm"
include "feqmptd.mm"
include "oveq2d.mm"
include "3eqtr3a.mm"
include "wceq.mm"
include "dvexp.mm"
include "oveq1.mm"
include "dvmptco.mm"

theorem dvsinexp
  let wph: wff ph
  let vx: setvar x
  let cN: class N
  let vy: setvar y
  let vk: setvar k
  assume dvsinexp.5: |- ( ph -> N e. NN )

  disjoint N x
  disjoint ph x
  disjoint x y
  disjoint N y
  disjoint ph y
  disjoint k x
  assert |- ( ph -> ( CC _D ( x e. CC |-> ( ( sin ` x ) ^ N ) ) ) = ( x e. CC |-> ( ( N x. ( ( sin ` x ) ^ ( N - 1 ) ) ) x. ( cos ` x ) ) ) )

  proof
    wph
    vx
    vy
    vx
    cv
    #
    csin
    cfv
    #
    @0
    ccos
    cfv
    #
    vy
    cv
    #
    cN
    cexp
    co
    #
    cN
    @3
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
    cc
    cc
    @1
    cN
    cexp
    co
    cN
    @1
    @5
    cexp
    co
    #
    cmul
    co
    cc
    cc
    cc
    cc
    cc
    cr
    cc
    cpr
    wcel
    wph
    cnelprrecn
    a1i
    #
    @9
    wph
    cc
    cc
    @0
    csin
    cc
    cc
    csin
    wf
    wph
    sinf
    a1i
    #
    ffvelrnda
    wph
    cc
    cc
    @0
    ccos
    cc
    cc
    ccos
    wf
    wph
    cosf
    a1i
    #
    ffvelrnda
    wph
    @3
    cc
    wcel
    #
    wa
    #
    @3
    cN
    wph
    @12
    simpr
    #
    wph
    cN
    cn0
    wcel
    @12
    wph
    cN
    dvsinexp.5
    nnnn0d
    adantr
    expcld
    @13
    cN
    @6
    wph
    cN
    cc
    wcel
    @12
    wph
    cN
    dvsinexp.5
    nncnd
    adantr
    @13
    @3
    @5
    @14
    wph
    @5
    cn0
    wcel
    #
    @12
    wph
    cN
    cn
    wcel
    #
    @15
    dvsinexp.5
    cN
    nnm1nn0
    syl
    adantr
    expcld
    mulcld
    wph
    cc
    csin
    cdv
    co
    ccos
    cc
    vx
    cc
    @1
    cmpt
    #
    cdv
    co
    vx
    cc
    @2
    cmpt
    dvsin
    wph
    csin
    @17
    cc
    cdv
    wph
    vx
    cc
    cc
    csin
    @10
    feqmptd
    oveq2d
    wph
    vx
    cc
    cc
    ccos
    @11
    feqmptd
    3eqtr3a
    wph
    @16
    cc
    vy
    cc
    @4
    cmpt
    cdv
    co
    vy
    cc
    @7
    cmpt
    wceq
    dvsinexp.5
    vy
    cN
    dvexp
    syl
    @3
    @1
    cN
    cexp
    oveq1
    @3
    @1
    wceq
    @6
    @8
    cN
    cmul
    @3
    @1
    @5
    cexp
    oveq1
    oveq2d
    dvmptco
end
