include "c2.mm"
include "cmul.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "c1.mm"
include "wne.mm"
include "cmin.mm"
include "clt.mm"
include "wbr.mm"
include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "1red.mm"
include "2re.mm"
include "a1i.mm"
include "cn.mm"
include "nnre.mm"
include "syl.mm"
include "remulcld.mm"
include "knoppndvlem3.mm"
include "simpld.mm"
include "recnd.mm"
include "abscld.mm"
include "1lt2.mm"
include "wceq.mm"
include "2t1e2.mm"
include "eqcomi.mm"
include "crp.mm"
include "2rp.mm"
include "ltmul2dd.mm"
include "eqbrtrd.mm"
include "mulassd.mm"
include "eqcomd.mm"
include "breqtrd.mm"
include "lttrd.mm"
include "jca.mm"
include "ltne.mm"
include "caddc.mm"
include "1p1e2.mm"
include "ltaddsubd.mm"
include "mpbid.mm"

theorem knoppndvlem12
  let wph: wff ph
  let cC: class C
  let cN: class N
  assume knoppndvlem12.c: |- ( ph -> C e. ( -u 1 (,) 1 ) )
  assume knoppndvlem12.n: |- ( ph -> N e. NN )
  assume knoppndvlem12.1: |- ( ph -> 1 < ( N x. ( abs ` C ) ) )


  assert |- ( ph -> ( ( ( 2 x. N ) x. ( abs ` C ) ) =/= 1 /\ 1 < ( ( ( 2 x. N ) x. ( abs ` C ) ) - 1 ) ) )

  proof
    wph
    c2
    cN
    cmul
    co
    #
    cC
    cabs
    cfv
    #
    cmul
    co
    #
    c1
    wne
    #
    c1
    @2
    c1
    cmin
    co
    clt
    wbr
    #
    wph
    c1
    cr
    wcel
    #
    c1
    @2
    clt
    wbr
    #
    wa
    @3
    wph
    @5
    @6
    wph
    1red
    #
    wph
    c1
    c2
    @2
    @7
    c2
    cr
    wcel
    wph
    2re
    a1i
    #
    wph
    @0
    @1
    wph
    c2
    cN
    @8
    wph
    cN
    cn
    wcel
    cN
    cr
    wcel
    knoppndvlem12.n
    cN
    nnre
    syl
    #
    remulcld
    wph
    cC
    wph
    cC
    wph
    cC
    cr
    wcel
    @1
    c1
    clt
    wbr
    wph
    cC
    knoppndvlem12.c
    knoppndvlem3
    simpld
    recnd
    abscld
    #
    remulcld
    #
    c1
    c2
    clt
    wbr
    wph
    1lt2
    a1i
    wph
    c2
    c2
    cN
    @1
    cmul
    co
    #
    cmul
    co
    #
    @2
    clt
    wph
    c2
    c2
    c1
    cmul
    co
    #
    @13
    clt
    c2
    @14
    wceq
    wph
    @14
    c2
    2t1e2
    eqcomi
    a1i
    wph
    c1
    @12
    c2
    @7
    wph
    cN
    @1
    @9
    @10
    remulcld
    c2
    crp
    wcel
    wph
    2rp
    a1i
    knoppndvlem12.1
    ltmul2dd
    eqbrtrd
    wph
    @2
    @13
    wph
    c2
    cN
    @1
    wph
    c2
    @8
    recnd
    wph
    cN
    @9
    recnd
    wph
    @1
    @10
    recnd
    mulassd
    eqcomd
    breqtrd
    #
    lttrd
    jca
    c1
    @2
    ltne
    syl
    wph
    c1
    c1
    caddc
    co
    #
    @2
    clt
    wbr
    @4
    wph
    @16
    c2
    @2
    clt
    @16
    c2
    wceq
    wph
    1p1e2
    a1i
    @15
    eqbrtrd
    wph
    c1
    c1
    @2
    @7
    @7
    @11
    ltaddsubd
    mpbid
    jca
end
