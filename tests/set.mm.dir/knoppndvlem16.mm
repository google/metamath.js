include "cmin.mm"
include "co.mm"
include "c2.mm"
include "cmul.mm"
include "cneg.mm"
include "cexp.mm"
include "cdiv.mm"
include "c1.mm"
include "caddc.mm"
include "wceq.mm"
include "a1i.mm"
include "oveq12d.mm"
include "2cnd.mm"
include "nncnd.mm"
include "mulcld.mm"
include "cc0.mm"
include "wne.mm"
include "2ne0.mm"
include "nnne0d.mm"
include "mulne0d.mm"
include "nn0zd.mm"
include "znegcld.mm"
include "expclzd.mm"
include "mulne0bad.mm"
include "divcld.mm"
include "zcnd.mm"
include "1cnd.mm"
include "addcld.mm"
include "subdid.mm"
include "eqcomd.mm"
include "pncan2d.mm"
include "oveq2d.mm"
include "mulid1d.mm"
include "eqtrd.mm"
include "3eqtrd.mm"

theorem knoppndvlem16
  let wph: wff ph
  let cA: class A
  let cB: class B
  let cJ: class J
  let cM: class M
  let cN: class N
  assume knoppndvlem16.a: |- A = ( ( ( ( 2 x. N ) ^ -u J ) / 2 ) x. M )
  assume knoppndvlem16.b: |- B = ( ( ( ( 2 x. N ) ^ -u J ) / 2 ) x. ( M + 1 ) )
  assume knoppndvlem16.j: |- ( ph -> J e. NN0 )
  assume knoppndvlem16.m: |- ( ph -> M e. ZZ )
  assume knoppndvlem16.n: |- ( ph -> N e. NN )


  assert |- ( ph -> ( B - A ) = ( ( ( 2 x. N ) ^ -u J ) / 2 ) )

  proof
    wph
    cB
    cA
    cmin
    co
    c2
    cN
    cmul
    co
    #
    cJ
    cneg
    #
    cexp
    co
    #
    c2
    cdiv
    co
    #
    cM
    c1
    caddc
    co
    #
    cmul
    co
    #
    @3
    cM
    cmul
    co
    #
    cmin
    co
    #
    @3
    @4
    cM
    cmin
    co
    #
    cmul
    co
    #
    @3
    wph
    cB
    @5
    cA
    @6
    cmin
    cB
    @5
    wceq
    wph
    knoppndvlem16.b
    a1i
    cA
    @6
    wceq
    wph
    knoppndvlem16.a
    a1i
    oveq12d
    wph
    @9
    @7
    wph
    @3
    @4
    cM
    wph
    @2
    c2
    wph
    @0
    @1
    wph
    c2
    cN
    wph
    2cnd
    #
    wph
    cN
    knoppndvlem16.n
    nncnd
    #
    mulcld
    wph
    c2
    cN
    @10
    @11
    c2
    cc0
    wne
    wph
    2ne0
    a1i
    wph
    cN
    knoppndvlem16.n
    nnne0d
    mulne0d
    #
    wph
    cJ
    wph
    cJ
    knoppndvlem16.j
    nn0zd
    znegcld
    expclzd
    @10
    wph
    c2
    cN
    @10
    @11
    @12
    mulne0bad
    divcld
    #
    wph
    cM
    c1
    wph
    cM
    knoppndvlem16.m
    zcnd
    #
    wph
    1cnd
    #
    addcld
    @14
    subdid
    eqcomd
    wph
    @9
    @3
    c1
    cmul
    co
    @3
    wph
    @8
    c1
    @3
    cmul
    wph
    cM
    c1
    @14
    @15
    pncan2d
    oveq2d
    wph
    @3
    @13
    mulid1d
    eqtrd
    3eqtrd
end
