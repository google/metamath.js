include "cv.mm"
include "cfv.mm"
include "c2.mm"
include "cmul.mm"
include "co.mm"
include "wceq.mm"
include "c1.mm"
include "cfz.mm"
include "wcel.mm"
include "wa.mm"
include "cdiv.mm"
include "clt.mm"
include "wbr.mm"
include "cmin.mm"
include "cif.mm"
include "cvv.mm"
include "cmpt.mm"
include "a1i.mm"
include "oveq1.mm"
include "breq1d.mm"
include "oveq2d.mm"
include "ifbieq12d.mm"
include "adantl.mm"
include "cn.mm"
include "cle.mm"
include "w3a.mm"
include "wi.mm"
include "elfz1b.mm"
include "cr.mm"
include "cc0.mm"
include "wb.mm"
include "nnre.mm"
include "adantr.mm"
include "2re.mm"
include "2pos.mm"
include "pm3.2i.mm"
include "lemul1.mm"
include "syl3anc.mm"
include "gausslemma2dlem0e.mm"
include "remulcld.mm"
include "gausslemma2dlem0a.mm"
include "nnred.mm"
include "rehalfcld.mm"
include "lelttr.mm"
include "syl2an3an.mm"
include "mpan2d.mm"
include "ex.mm"
include "com23.mm"
include "sylbid.mm"
include "3impia.mm"
include "sylbi.mm"
include "impcom.mm"
include "iftrued.mm"
include "eqtrd.mm"
include "cuz.mm"
include "wss.mm"
include "cz.mm"
include "gausslemma2dlem0d.mm"
include "nn0zd.mm"
include "gausslemma2dlem0b.mm"
include "nnzd.mm"
include "gausslemma2dlem0g.mm"
include "eluz2.mm"
include "syl3anbrc.mm"
include "fzss2.mm"
include "syl.mm"
include "sselda.mm"
include "ovexd.mm"
include "fvmptd.mm"
include "ralrimiva.mm"

theorem gausslemma2dlem2
  let wph: wff ph
  let vx: setvar x
  let cP: class P
  let cR: class R
  let vk: setvar k
  let cH: class H
  let cM: class M
  let vy: setvar y
  let vl: setvar l
  assume gausslemma2d.p: |- ( ph -> P e. ( Prime \ { 2 } ) )
  assume gausslemma2d.h: |- H = ( ( P - 1 ) / 2 )
  assume gausslemma2d.r: |- R = ( x e. ( 1 ... H ) |-> if ( ( x x. 2 ) < ( P / 2 ) , ( x x. 2 ) , ( P - ( x x. 2 ) ) ) )
  assume gausslemma2d.m: |- M = ( |_ ` ( P / 4 ) )

  disjoint H x
  disjoint P x
  disjoint ph x
  disjoint H k
  disjoint R k
  disjoint k ph
  disjoint M x
  disjoint k x
  disjoint H y
  disjoint x y
  disjoint R y
  disjoint ph y
  disjoint H l
  disjoint k l
  disjoint R l
  disjoint l ph
  assert |- ( ph -> A. k e. ( 1 ... M ) ( R ` k ) = ( k x. 2 ) )

  proof
    wph
    vk
    cv
    #
    cR
    cfv
    @0
    c2
    cmul
    co
    #
    wceq
    vk
    c1
    cM
    cfz
    co
    #
    wph
    @0
    @2
    wcel
    #
    wa
    #
    vx
    @0
    vx
    cv
    #
    c2
    cmul
    co
    #
    cP
    c2
    cdiv
    co
    #
    clt
    wbr
    #
    @6
    cP
    @6
    cmin
    co
    #
    cif
    #
    @1
    c1
    cH
    cfz
    co
    #
    cR
    cvv
    cR
    vx
    @11
    @10
    cmpt
    wceq
    @4
    gausslemma2d.r
    a1i
    @4
    @5
    @0
    wceq
    #
    wa
    #
    @10
    @1
    @7
    clt
    wbr
    #
    @1
    cP
    @1
    cmin
    co
    #
    cif
    #
    @1
    @12
    @10
    @16
    wceq
    @4
    @12
    @8
    @14
    @6
    @9
    @1
    @15
    @12
    @6
    @1
    @7
    clt
    @5
    @0
    c2
    cmul
    oveq1
    #
    breq1d
    @17
    @12
    @6
    @1
    cP
    cmin
    @17
    oveq2d
    ifbieq12d
    adantl
    @13
    @14
    @1
    @15
    @4
    @14
    @12
    @3
    wph
    @14
    @3
    @0
    cn
    wcel
    #
    cM
    cn
    wcel
    #
    @0
    cM
    cle
    wbr
    #
    w3a
    wph
    @14
    wi
    #
    cM
    @0
    elfz1b
    @18
    @19
    @20
    @21
    @18
    @19
    wa
    #
    @20
    @1
    cM
    c2
    cmul
    co
    #
    cle
    wbr
    #
    @21
    @22
    @0
    cr
    wcel
    #
    cM
    cr
    wcel
    #
    c2
    cr
    wcel
    #
    cc0
    c2
    clt
    wbr
    #
    wa
    #
    @20
    @24
    wb
    @18
    @25
    @19
    @0
    nnre
    #
    adantr
    @19
    @26
    @18
    cM
    nnre
    #
    adantl
    @29
    @22
    @27
    @28
    2re
    2pos
    pm3.2i
    a1i
    @0
    cM
    c2
    lemul1
    syl3anc
    @22
    wph
    @24
    @14
    @22
    wph
    @24
    @14
    wi
    @22
    wph
    wa
    @24
    @23
    @7
    clt
    wbr
    #
    @14
    wph
    @32
    @22
    wph
    cP
    cM
    gausslemma2d.p
    gausslemma2d.m
    gausslemma2dlem0e
    adantl
    @22
    @1
    cr
    wcel
    #
    @23
    cr
    wcel
    #
    wph
    @7
    cr
    wcel
    @24
    @32
    wa
    @14
    wi
    @18
    @33
    @19
    @18
    @0
    c2
    @30
    @27
    @18
    2re
    a1i
    remulcld
    adantr
    @19
    @34
    @18
    @19
    cM
    c2
    @31
    @27
    @19
    2re
    a1i
    remulcld
    adantl
    wph
    cP
    wph
    cP
    wph
    cP
    gausslemma2d.p
    gausslemma2dlem0a
    nnred
    rehalfcld
    @1
    @23
    @7
    lelttr
    syl2an3an
    mpan2d
    ex
    com23
    sylbid
    3impia
    sylbi
    impcom
    adantr
    iftrued
    eqtrd
    wph
    @2
    @11
    @0
    wph
    cH
    cM
    cuz
    cfv
    wcel
    #
    @2
    @11
    wss
    wph
    cM
    cz
    wcel
    cH
    cz
    wcel
    cM
    cH
    cle
    wbr
    @35
    wph
    cM
    wph
    cP
    cM
    gausslemma2d.p
    gausslemma2d.m
    gausslemma2dlem0d
    nn0zd
    wph
    cH
    wph
    cP
    cH
    gausslemma2d.p
    gausslemma2d.h
    gausslemma2dlem0b
    nnzd
    wph
    cP
    cH
    cM
    gausslemma2d.p
    gausslemma2d.m
    gausslemma2d.h
    gausslemma2dlem0g
    cM
    cH
    eluz2
    syl3anbrc
    cM
    c1
    cH
    fzss2
    syl
    sselda
    @4
    @0
    c2
    cmul
    ovexd
    fvmptd
    ralrimiva
end
