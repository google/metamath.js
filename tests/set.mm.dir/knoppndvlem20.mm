include "c1.mm"
include "c2.mm"
include "cmul.mm"
include "co.mm"
include "cabs.mm"
include "cfv.mm"
include "cmin.mm"
include "cdiv.mm"
include "clt.mm"
include "wbr.mm"
include "crp.mm"
include "wcel.mm"
include "wne.mm"
include "knoppndvlem12.mm"
include "simprd.mm"
include "cr.mm"
include "2re.mm"
include "a1i.mm"
include "nnred.mm"
include "remulcld.mm"
include "knoppndvlem3.mm"
include "simpld.mm"
include "recnd.mm"
include "abscld.mm"
include "1red.mm"
include "resubcld.mm"
include "cc0.mm"
include "0red.mm"
include "0lt1.mm"
include "lttrd.mm"
include "elrpd.mm"
include "recgt1d.mm"
include "mpbid.mm"
include "wa.mm"
include "wb.mm"
include "rprecred.mm"
include "jca.mm"
include "difrp.mm"
include "syl.mm"

theorem knoppndvlem20
  let wph: wff ph
  let cC: class C
  let cN: class N
  assume knoppndvlem20.c: |- ( ph -> C e. ( -u 1 (,) 1 ) )
  assume knoppndvlem20.n: |- ( ph -> N e. NN )
  assume knoppndvlem20.1: |- ( ph -> 1 < ( N x. ( abs ` C ) ) )


  assert |- ( ph -> ( 1 - ( 1 / ( ( ( 2 x. N ) x. ( abs ` C ) ) - 1 ) ) ) e. RR+ )

  proof
    wph
    c1
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
    cmin
    co
    #
    cdiv
    co
    #
    c1
    clt
    wbr
    #
    c1
    @4
    cmin
    co
    crp
    wcel
    #
    wph
    c1
    @3
    clt
    wbr
    #
    @5
    wph
    @2
    c1
    wne
    @7
    wph
    cC
    cN
    knoppndvlem20.c
    knoppndvlem20.n
    knoppndvlem20.1
    knoppndvlem12
    simprd
    #
    wph
    @3
    wph
    @3
    wph
    @2
    c1
    wph
    @0
    @1
    wph
    c2
    cN
    c2
    cr
    wcel
    wph
    2re
    a1i
    wph
    cN
    knoppndvlem20.n
    nnred
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
    knoppndvlem20.c
    knoppndvlem3
    simpld
    recnd
    abscld
    remulcld
    wph
    1red
    #
    resubcld
    #
    wph
    cc0
    c1
    @3
    wph
    0red
    @9
    @10
    cc0
    c1
    clt
    wbr
    wph
    0lt1
    a1i
    @8
    lttrd
    elrpd
    #
    recgt1d
    mpbid
    wph
    @4
    cr
    wcel
    #
    c1
    cr
    wcel
    #
    wa
    @5
    @6
    wb
    wph
    @12
    @13
    wph
    @3
    @11
    rprecred
    @9
    jca
    @4
    c1
    difrp
    syl
    mpbid
end
