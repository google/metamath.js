include "cfa.mm"
include "cfv.mm"
include "cgcd.mm"
include "co.mm"
include "c1.mm"
include "wceq.mm"
include "cdvds.mm"
include "wbr.mm"
include "wn.mm"
include "cprime.mm"
include "wcel.mm"
include "cn0.mm"
include "wa.mm"
include "clt.mm"
include "c2.mm"
include "csn.mm"
include "cdif.mm"
include "eldifi.mm"
include "syl.mm"
include "gausslemma2dlem0b.mm"
include "nnnn0d.mm"
include "jca.mm"
include "cmin.mm"
include "cdiv.mm"
include "cn.mm"
include "prmnn.mm"
include "cmul.mm"
include "cr.mm"
include "nnre.mm"
include "peano2rem.mm"
include "2re.mm"
include "a1i.mm"
include "remulcld.mm"
include "ltm1d.mm"
include "nnnn0.mm"
include "nn0ge0d.mm"
include "cle.mm"
include "1le2.mm"
include "lemulge12d.mm"
include "ltletrd.mm"
include "cc0.mm"
include "wb.mm"
include "2pos.mm"
include "pm3.2i.mm"
include "ltdivmul.mm"
include "syl3anc.mm"
include "mpbird.mm"
include "3syl.mm"
include "syl5eqbr.mm"
include "prmndvdsfaclt.mm"
include "sylc.mm"
include "cz.mm"
include "faccld.mm"
include "nnzd.mm"
include "nnz.mm"
include "gcdcom.mm"
include "syl2anc.mm"
include "eqeq1d.mm"
include "coprm.mm"
include "bitr4d.mm"

theorem gausslemma2dlem0c
  let wph: wff ph
  let cP: class P
  let cH: class H
  assume gausslemma2dlem0a.p: |- ( ph -> P e. ( Prime \ { 2 } ) )
  assume gausslemma2dlem0b.h: |- H = ( ( P - 1 ) / 2 )


  assert |- ( ph -> ( ( ! ` H ) gcd P ) = 1 )

  proof
    wph
    cH
    cfa
    cfv
    #
    cP
    cgcd
    co
    #
    c1
    wceq
    #
    cP
    @0
    cdvds
    wbr
    wn
    #
    wph
    cP
    cprime
    wcel
    #
    cH
    cn0
    wcel
    #
    wa
    cH
    cP
    clt
    wbr
    @3
    wph
    @4
    @5
    wph
    cP
    cprime
    c2
    csn
    #
    cdif
    wcel
    #
    @4
    gausslemma2dlem0a.p
    cP
    cprime
    @6
    eldifi
    #
    syl
    #
    wph
    cH
    wph
    cP
    cH
    gausslemma2dlem0a.p
    gausslemma2dlem0b.h
    gausslemma2dlem0b
    nnnn0d
    #
    jca
    wph
    cH
    cP
    c1
    cmin
    co
    #
    c2
    cdiv
    co
    #
    cP
    clt
    gausslemma2dlem0b.h
    wph
    @7
    @12
    cP
    clt
    wbr
    #
    gausslemma2dlem0a.p
    @7
    @4
    cP
    cn
    wcel
    #
    @13
    @8
    cP
    prmnn
    #
    @14
    @13
    @11
    c2
    cP
    cmul
    co
    #
    clt
    wbr
    #
    @14
    @11
    cP
    @16
    @14
    cP
    cr
    wcel
    #
    @11
    cr
    wcel
    #
    cP
    nnre
    #
    cP
    peano2rem
    syl
    #
    @20
    @14
    c2
    cP
    c2
    cr
    wcel
    #
    @14
    2re
    a1i
    #
    @20
    remulcld
    @14
    cP
    @20
    ltm1d
    @14
    cP
    c2
    @20
    @23
    @14
    cP
    cP
    nnnn0
    nn0ge0d
    c1
    c2
    cle
    wbr
    @14
    1le2
    a1i
    lemulge12d
    ltletrd
    @14
    @19
    @18
    @22
    cc0
    c2
    clt
    wbr
    #
    wa
    #
    @13
    @17
    wb
    @21
    @20
    @25
    @14
    @22
    @24
    2re
    2pos
    pm3.2i
    a1i
    @11
    cP
    c2
    ltdivmul
    syl3anc
    mpbird
    3syl
    syl
    syl5eqbr
    cP
    cH
    prmndvdsfaclt
    sylc
    wph
    @2
    cP
    @0
    cgcd
    co
    #
    c1
    wceq
    #
    @3
    wph
    @1
    @26
    c1
    wph
    @0
    cz
    wcel
    #
    cP
    cz
    wcel
    #
    @1
    @26
    wceq
    wph
    @0
    wph
    cH
    @10
    faccld
    nnzd
    #
    wph
    @7
    @29
    gausslemma2dlem0a.p
    @7
    @4
    @14
    @29
    @8
    @15
    cP
    nnz
    3syl
    syl
    @0
    cP
    gcdcom
    syl2anc
    eqeq1d
    wph
    @4
    @28
    @3
    @27
    wb
    @9
    @30
    cP
    @0
    coprm
    syl2anc
    bitr4d
    mpbird
end
