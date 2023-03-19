include "c2.mm"
include "cmul.mm"
include "co.mm"
include "cexp.mm"
include "cmin.mm"
include "c1.mm"
include "cz.mm"
include "wcel.mm"
include "cc0.mm"
include "clt.mm"
include "wbr.mm"
include "cn.mm"
include "2z.mm"
include "cuz.mm"
include "cfv.mm"
include "eluzelz.mm"
include "syl.mm"
include "zmulcl.mm"
include "sylancr.mm"
include "eluz2nn.mm"
include "nnzd.mm"
include "zmulcld.mm"
include "zsqcl.mm"
include "zsubcld.mm"
include "peano2zm.mm"
include "0red.mm"
include "nnnn0d.mm"
include "nnexpcld.mm"
include "nnred.mm"
include "zred.mm"
include "nngt0d.mm"
include "jm3.1lem2.mm"
include "lttrd.mm"
include "elnnz.mm"
include "sylanbrc.mm"

theorem jm3.1lem3
  let wph: wff ph
  let cA: class A
  let cK: class K
  let cN: class N
  assume jm3.1.a: |- ( ph -> A e. ( ZZ>= ` 2 ) )
  assume jm3.1.b: |- ( ph -> K e. ( ZZ>= ` 2 ) )
  assume jm3.1.c: |- ( ph -> N e. NN )
  assume jm3.1.d: |- ( ph -> ( K rmY ( N + 1 ) ) <_ A )


  assert |- ( ph -> ( ( ( ( 2 x. A ) x. K ) - ( K ^ 2 ) ) - 1 ) e. NN )

  proof
    wph
    c2
    cA
    cmul
    co
    #
    cK
    cmul
    co
    #
    cK
    c2
    cexp
    co
    #
    cmin
    co
    #
    c1
    cmin
    co
    #
    cz
    wcel
    #
    cc0
    @4
    clt
    wbr
    @4
    cn
    wcel
    wph
    @3
    cz
    wcel
    @5
    wph
    @1
    @2
    wph
    @0
    cK
    wph
    c2
    cz
    wcel
    cA
    cz
    wcel
    #
    @0
    cz
    wcel
    2z
    wph
    cA
    c2
    cuz
    cfv
    #
    wcel
    @6
    jm3.1.a
    c2
    cA
    eluzelz
    syl
    c2
    cA
    zmulcl
    sylancr
    wph
    cK
    wph
    cK
    @7
    wcel
    cK
    cn
    wcel
    jm3.1.b
    cK
    eluz2nn
    syl
    #
    nnzd
    #
    zmulcld
    wph
    cK
    cz
    wcel
    @2
    cz
    wcel
    @9
    cK
    zsqcl
    syl
    zsubcld
    @3
    peano2zm
    syl
    #
    wph
    cc0
    cK
    cN
    cexp
    co
    #
    @4
    wph
    0red
    wph
    @11
    wph
    cK
    cN
    @8
    wph
    cN
    jm3.1.c
    nnnn0d
    nnexpcld
    #
    nnred
    wph
    @4
    @10
    zred
    wph
    @11
    @12
    nngt0d
    wph
    cA
    cK
    cN
    jm3.1.a
    jm3.1.b
    jm3.1.c
    jm3.1.d
    jm3.1lem2
    lttrd
    @4
    elnnz
    sylanbrc
end
