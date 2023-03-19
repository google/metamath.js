include "c1.mm"
include "co.mm"
include "cmin.mm"
include "cs2.mm"
include "cfv.mm"
include "cc0.mm"
include "c2.mm"
include "cn.mm"
include "wcel.mm"
include "2nn.mm"
include "a1i.mm"
include "cword.mm"
include "s2cld.mm"
include "chash.mm"
include "wceq.mm"
include "s2len.mm"
include "lmat22lem.mm"
include "cfz.mm"
include "cuz.mm"
include "2eluzge1.mm"
include "eluzfz1.mm"
include "ax-mp.mm"
include "lmatfval.mm"
include "1m1e0.mm"
include "fveq2i.mm"
include "s2fv0.mm"
include "syl.mm"
include "syl5eq.mm"
include "fveq12d.mm"
include "3eqtrd.mm"

theorem lmat22e11
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cC: class C
  let cD: class D
  let cM: class M
  let cV: class V
  let vi: setvar i
  assume lmat22.m: |- M = ( litMat ` <" <" A B "> <" C D "> "> )
  assume lmat22.a: |- ( ph -> A e. V )
  assume lmat22.b: |- ( ph -> B e. V )
  assume lmat22.c: |- ( ph -> C e. V )
  assume lmat22.d: |- ( ph -> D e. V )


  assert |- ( ph -> ( 1 M 1 ) = A )

  proof
    wph
    c1
    c1
    cM
    co
    c1
    c1
    cmin
    co
    #
    @0
    cA
    cB
    cs2
    #
    cC
    cD
    cs2
    #
    cs2
    #
    cfv
    #
    cfv
    cc0
    @1
    cfv
    #
    cA
    wph
    vi
    c1
    c1
    cM
    c2
    cV
    @3
    lmat22.m
    c2
    cn
    wcel
    wph
    2nn
    a1i
    wph
    @1
    @2
    cV
    cword
    #
    wph
    cA
    cB
    cV
    lmat22.a
    lmat22.b
    s2cld
    #
    wph
    cC
    cD
    cV
    lmat22.c
    lmat22.d
    s2cld
    s2cld
    @3
    chash
    cfv
    c2
    wceq
    wph
    @1
    @2
    s2len
    a1i
    wph
    cA
    cB
    cC
    cD
    vi
    cM
    cV
    lmat22.m
    lmat22.a
    lmat22.b
    lmat22.c
    lmat22.d
    lmat22lem
    c1
    c1
    c2
    cfz
    co
    wcel
    #
    wph
    c2
    c1
    cuz
    cfv
    wcel
    @8
    2eluzge1
    c1
    c2
    eluzfz1
    ax-mp
    a1i
    #
    @9
    lmatfval
    wph
    @0
    cc0
    @4
    @1
    wph
    @4
    cc0
    @3
    cfv
    #
    @1
    @0
    cc0
    @3
    1m1e0
    fveq2i
    wph
    @1
    @6
    wcel
    @10
    @1
    wceq
    @7
    @1
    @2
    @6
    s2fv0
    syl
    syl5eq
    @0
    cc0
    wceq
    wph
    1m1e0
    a1i
    fveq12d
    wph
    cA
    cV
    wcel
    @5
    cA
    wceq
    lmat22.a
    cA
    cB
    cV
    s2fv0
    syl
    3eqtrd
end
