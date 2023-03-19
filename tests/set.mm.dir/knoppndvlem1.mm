include "c2.mm"
include "cmul.mm"
include "co.mm"
include "cneg.mm"
include "cexp.mm"
include "cdiv.mm"
include "cr.mm"
include "wcel.mm"
include "2re.mm"
include "a1i.mm"
include "cn.mm"
include "cz.mm"
include "nnz.mm"
include "syl.mm"
include "zred.mm"
include "remulcld.mm"
include "recnd.mm"
include "cc0.mm"
include "wne.mm"
include "2ne0.mm"
include "0red.mm"
include "c1.mm"
include "1red.mm"
include "clt.mm"
include "wbr.mm"
include "0lt1.mm"
include "cle.mm"
include "nnge1.mm"
include "ltletrd.mm"
include "ltned.mm"
include "necomd.mm"
include "mulne0d.mm"
include "znegcld.mm"
include "reexpclzd.mm"
include "redivcld.mm"

theorem knoppndvlem1
  let wph: wff ph
  let cJ: class J
  let cM: class M
  let cN: class N
  assume knoppndvlem1.n: |- ( ph -> N e. NN )
  assume knoppndvlem1.j: |- ( ph -> J e. ZZ )
  assume knoppndvlem1.m: |- ( ph -> M e. ZZ )


  assert |- ( ph -> ( ( ( ( 2 x. N ) ^ -u J ) / 2 ) x. M ) e. RR )

  proof
    wph
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
    c2
    cr
    wcel
    wph
    2re
    a1i
    #
    wph
    cN
    wph
    cN
    cn
    wcel
    #
    cN
    cz
    wcel
    knoppndvlem1.n
    cN
    nnz
    syl
    zred
    #
    remulcld
    wph
    c2
    cN
    wph
    c2
    @3
    recnd
    wph
    cN
    @5
    recnd
    c2
    cc0
    wne
    wph
    2ne0
    a1i
    #
    wph
    cc0
    cN
    wph
    cc0
    cN
    wph
    0red
    #
    wph
    cc0
    c1
    cN
    @7
    wph
    1red
    @5
    cc0
    c1
    clt
    wbr
    wph
    0lt1
    a1i
    wph
    @4
    c1
    cN
    cle
    wbr
    knoppndvlem1.n
    cN
    nnge1
    syl
    ltletrd
    ltned
    necomd
    mulne0d
    wph
    cJ
    knoppndvlem1.j
    znegcld
    reexpclzd
    @3
    @6
    redivcld
    wph
    cM
    knoppndvlem1.m
    zred
    remulcld
end
