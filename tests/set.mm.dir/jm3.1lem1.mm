include "cexp.mm"
include "co.mm"
include "c2.mm"
include "cmul.mm"
include "c1.mm"
include "cmin.mm"
include "cuz.mm"
include "cfv.mm"
include "wcel.mm"
include "cr.mm"
include "eluzelre.mm"
include "syl.mm"
include "nnnn0d.mm"
include "reexpcld.mm"
include "cn.mm"
include "cz.mm"
include "2z.mm"
include "uzid.mm"
include "ax-mp.mm"
include "uz2mulcl.mm"
include "sylancr.mm"
include "uz2m1nn.mm"
include "nnred.mm"
include "clt.mm"
include "wbr.mm"
include "cc0.mm"
include "nngt0d.mm"
include "cc.mm"
include "2cn.mm"
include "recnd.mm"
include "mulcl.mm"
include "1cnd.mm"
include "sub32d.mm"
include "caddc.mm"
include "2timesd.mm"
include "oveq1d.mm"
include "pncand.mm"
include "eqtrd.mm"
include "breqtrrd.mm"
include "posdifd.mm"
include "mpbird.mm"
include "crp.mm"
include "wb.mm"
include "eluz2nn.mm"
include "nnrpd.mm"
include "rpexpmord.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "crmy.mm"
include "nnzd.mm"
include "peano2zd.mm"
include "frmy.mm"
include "fovcl.mm"
include "syl2anc.mm"
include "zred.mm"
include "cn0.mm"
include "cle.mm"
include "jm2.17a.mm"
include "letrd.mm"
include "ltletrd.mm"

theorem jm3.1lem1
  let wph: wff ph
  let cA: class A
  let cK: class K
  let cN: class N
  assume jm3.1.a: |- ( ph -> A e. ( ZZ>= ` 2 ) )
  assume jm3.1.b: |- ( ph -> K e. ( ZZ>= ` 2 ) )
  assume jm3.1.c: |- ( ph -> N e. NN )
  assume jm3.1.d: |- ( ph -> ( K rmY ( N + 1 ) ) <_ A )


  assert |- ( ph -> ( K ^ N ) < A )

  proof
    wph
    cK
    cN
    cexp
    co
    #
    c2
    cK
    cmul
    co
    #
    c1
    cmin
    co
    #
    cN
    cexp
    co
    #
    cA
    wph
    cK
    cN
    wph
    cK
    c2
    cuz
    cfv
    #
    wcel
    #
    cK
    cr
    wcel
    jm3.1.b
    c2
    cK
    eluzelre
    syl
    #
    wph
    cN
    jm3.1.c
    nnnn0d
    #
    reexpcld
    wph
    @2
    cN
    wph
    @2
    wph
    @1
    @4
    wcel
    #
    @2
    cn
    wcel
    wph
    c2
    @4
    wcel
    #
    @5
    @8
    c2
    cz
    wcel
    @9
    2z
    c2
    uzid
    ax-mp
    jm3.1.b
    c2
    cK
    uz2mulcl
    sylancr
    @1
    uz2m1nn
    syl
    #
    nnred
    #
    @7
    reexpcld
    #
    wph
    cA
    @4
    wcel
    cA
    cr
    wcel
    jm3.1.a
    c2
    cA
    eluzelre
    syl
    #
    wph
    cK
    @2
    clt
    wbr
    #
    @0
    @3
    clt
    wbr
    #
    wph
    @14
    cc0
    @2
    cK
    cmin
    co
    #
    clt
    wbr
    wph
    cc0
    cK
    c1
    cmin
    co
    #
    @16
    clt
    wph
    @17
    wph
    @5
    @17
    cn
    wcel
    jm3.1.b
    cK
    uz2m1nn
    syl
    nngt0d
    wph
    @16
    @1
    cK
    cmin
    co
    #
    c1
    cmin
    co
    @17
    wph
    @1
    c1
    cK
    wph
    c2
    cc
    wcel
    cK
    cc
    wcel
    @1
    cc
    wcel
    2cn
    wph
    cK
    @6
    recnd
    #
    c2
    cK
    mulcl
    sylancr
    wph
    1cnd
    @19
    sub32d
    wph
    @18
    cK
    c1
    cmin
    wph
    @18
    cK
    cK
    caddc
    co
    #
    cK
    cmin
    co
    cK
    wph
    @1
    @20
    cK
    cmin
    wph
    cK
    @19
    2timesd
    oveq1d
    wph
    cK
    cK
    @19
    @19
    pncand
    eqtrd
    oveq1d
    eqtrd
    breqtrrd
    wph
    cK
    @2
    @6
    @11
    posdifd
    mpbird
    wph
    cN
    cn
    wcel
    cK
    crp
    wcel
    @2
    crp
    wcel
    @14
    @15
    wb
    jm3.1.c
    wph
    cK
    wph
    @5
    cK
    cn
    wcel
    jm3.1.b
    cK
    eluz2nn
    syl
    nnrpd
    wph
    @2
    @10
    nnrpd
    cK
    @2
    cN
    rpexpmord
    syl3anc
    mpbid
    wph
    @3
    cK
    cN
    c1
    caddc
    co
    #
    crmy
    co
    #
    cA
    @12
    wph
    @22
    wph
    @5
    @21
    cz
    wcel
    @22
    cz
    wcel
    jm3.1.b
    wph
    cN
    wph
    cN
    jm3.1.c
    nnzd
    peano2zd
    cK
    @21
    cz
    @4
    cz
    crmy
    frmy
    fovcl
    syl2anc
    zred
    @13
    wph
    @5
    cN
    cn0
    wcel
    @3
    @22
    cle
    wbr
    jm3.1.b
    @7
    cK
    cN
    jm2.17a
    syl2anc
    jm3.1.d
    letrd
    ltletrd
end
