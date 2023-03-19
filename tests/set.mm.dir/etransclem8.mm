include "cv.mm"
include "c1.mm"
include "cmin.mm"
include "co.mm"
include "cexp.mm"
include "cfz.mm"
include "cprod.mm"
include "cmul.mm"
include "cc.mm"
include "wcel.mm"
include "wa.mm"
include "sselda.mm"
include "cn.mm"
include "cn0.mm"
include "adantr.mm"
include "nnm1nn0.mm"
include "syl.mm"
include "expcld.mm"
include "fzfid.mm"
include "elfzelz.mm"
include "zcnd.mm"
include "adantl.mm"
include "subcld.mm"
include "nnnn0d.mm"
include "ad2antrr.mm"
include "fprodcl.mm"
include "mulcld.mm"
include "fmptd.mm"

theorem etransclem8
  let wph: wff ph
  let vx: setvar x
  let cP: class P
  let vj: setvar j
  let cF: class F
  let cM: class M
  let cX: class X
  let vk: setvar k
  assume etransclem8.x: |- ( ph -> X C_ CC )
  assume etransclem8.p: |- ( ph -> P e. NN )
  assume etransclem8.f: |- F = ( x e. X |-> ( ( x ^ ( P - 1 ) ) x. prod_ j e. ( 1 ... M ) ( ( x - j ) ^ P ) ) )

  disjoint M j
  disjoint X j
  disjoint X x
  disjoint j x
  disjoint j ph
  disjoint ph x
  disjoint k x
  assert |- ( ph -> F : X --> CC )

  proof
    wph
    vx
    cX
    vx
    cv
    #
    cP
    c1
    cmin
    co
    #
    cexp
    co
    #
    c1
    cM
    cfz
    co
    #
    @0
    vj
    cv
    #
    cmin
    co
    #
    cP
    cexp
    co
    #
    vj
    cprod
    #
    cmul
    co
    cc
    cF
    wph
    @0
    cX
    wcel
    #
    wa
    #
    @2
    @7
    @9
    @0
    @1
    wph
    cX
    cc
    @0
    etransclem8.x
    sselda
    #
    @9
    cP
    cn
    wcel
    #
    @1
    cn0
    wcel
    wph
    @11
    @8
    etransclem8.p
    adantr
    cP
    nnm1nn0
    syl
    expcld
    @9
    @3
    @6
    vj
    @9
    c1
    cM
    fzfid
    @9
    @4
    @3
    wcel
    #
    wa
    #
    @5
    cP
    @13
    @0
    @4
    @9
    @0
    cc
    wcel
    @12
    @10
    adantr
    @12
    @4
    cc
    wcel
    @9
    @12
    @4
    @4
    c1
    cM
    elfzelz
    zcnd
    adantl
    subcld
    wph
    cP
    cn0
    wcel
    @8
    @12
    wph
    cP
    etransclem8.p
    nnnn0d
    ad2antrr
    expcld
    fprodcl
    mulcld
    etransclem8.f
    fmptd
end
