include "cfa.mm"
include "cfv.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "cprod.mm"
include "cdiv.mm"
include "c1.mm"
include "cmin.mm"
include "clt.mm"
include "wbr.mm"
include "cexp.mm"
include "cmul.mm"
include "cif.mm"
include "cneg.mm"
include "wn.mm"
include "wceq.mm"
include "wa.mm"
include "cr.mm"
include "fzssre.mm"
include "cuz.mm"
include "wcel.mm"
include "cn0.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "eluzfz1.mm"
include "syl.mm"
include "ffvelrnd.mm"
include "sseldi.mm"
include "eqeltrrd.mm"
include "lttri3d.mm"
include "mpbid.mm"
include "simprd.mm"
include "iffalsed.mm"
include "recnd.mm"
include "eqcomd.mm"
include "subeq0bd.mm"
include "fveq2d.mm"
include "fac0.mm"
include "syl6eq.mm"
include "oveq2d.mm"
include "cn.mm"
include "nnm1nn0.mm"
include "faccld.mm"
include "nncnd.mm"
include "div1d.mm"
include "eqtrd.mm"
include "oveq12d.mm"
include "0exp0e1.mm"
include "mulid1d.mm"
include "3eqtrd.mm"
include "oveq1d.mm"
include "df-neg.mm"
include "syl6eqr.mm"
include "ifeq2d.mm"
include "prodeq2ad.mm"
include "syl5eq.mm"

theorem etransclem14
  let wph: wff ph
  let cC: class C
  let cP: class P
  let cT: class T
  let vj: setvar j
  let cJ: class J
  let cM: class M
  let cN: class N
  let vk: setvar k
  let vx: setvar x
  assume etransclem14.n: |- ( ph -> P e. NN )
  assume etransclem14.m: |- ( ph -> M e. NN0 )
  assume etransclem14.c: |- ( ph -> C : ( 0 ... M ) --> ( 0 ... N ) )
  assume etransclem14.t: |- T = ( ( ( ! ` N ) / prod_ j e. ( 0 ... M ) ( ! ` ( C ` j ) ) ) x. ( if ( ( P - 1 ) < ( C ` 0 ) , 0 , ( ( ( ! ` ( P - 1 ) ) / ( ! ` ( ( P - 1 ) - ( C ` 0 ) ) ) ) x. ( J ^ ( ( P - 1 ) - ( C ` 0 ) ) ) ) ) x. prod_ j e. ( 1 ... M ) if ( P < ( C ` j ) , 0 , ( ( ( ! ` P ) / ( ! ` ( P - ( C ` j ) ) ) ) x. ( ( J - j ) ^ ( P - ( C ` j ) ) ) ) ) ) )
  assume etransclem14.j: |- ( ph -> J = 0 )
  assume etransclem14.cpm1: |- ( ph -> ( C ` 0 ) = ( P - 1 ) )

  disjoint M j
  disjoint j ph
  disjoint k x
  assert |- ( ph -> T = ( ( ( ! ` N ) / prod_ j e. ( 0 ... M ) ( ! ` ( C ` j ) ) ) x. ( ( ! ` ( P - 1 ) ) x. prod_ j e. ( 1 ... M ) if ( P < ( C ` j ) , 0 , ( ( ( ! ` P ) / ( ! ` ( P - ( C ` j ) ) ) ) x. ( -u j ^ ( P - ( C ` j ) ) ) ) ) ) ) )

  proof
    wph
    cT
    cN
    cfa
    cfv
    cc0
    cM
    cfz
    co
    #
    vj
    cv
    #
    cC
    cfv
    #
    cfa
    cfv
    vj
    cprod
    cdiv
    co
    #
    cP
    c1
    cmin
    co
    #
    cc0
    cC
    cfv
    #
    clt
    wbr
    #
    cc0
    @4
    cfa
    cfv
    #
    @4
    @5
    cmin
    co
    #
    cfa
    cfv
    #
    cdiv
    co
    #
    cJ
    @8
    cexp
    co
    #
    cmul
    co
    #
    cif
    #
    c1
    cM
    cfz
    co
    #
    cP
    @2
    clt
    wbr
    #
    cc0
    cP
    cfa
    cfv
    cP
    @2
    cmin
    co
    #
    cfa
    cfv
    cdiv
    co
    #
    cJ
    @1
    cmin
    co
    #
    @16
    cexp
    co
    #
    cmul
    co
    #
    cif
    #
    vj
    cprod
    #
    cmul
    co
    #
    cmul
    co
    @3
    @7
    @14
    @15
    cc0
    @17
    @1
    cneg
    #
    @16
    cexp
    co
    #
    cmul
    co
    #
    cif
    #
    vj
    cprod
    #
    cmul
    co
    #
    cmul
    co
    etransclem14.t
    wph
    @23
    @29
    @3
    cmul
    wph
    @13
    @7
    @22
    @28
    cmul
    wph
    @13
    @12
    @7
    c1
    cmul
    co
    @7
    wph
    @6
    cc0
    @12
    wph
    @5
    @4
    clt
    wbr
    wn
    #
    @6
    wn
    #
    wph
    @5
    @4
    wceq
    @30
    @31
    wa
    etransclem14.cpm1
    wph
    @5
    @4
    wph
    cc0
    cN
    cfz
    co
    #
    cr
    @5
    cc0
    cN
    fzssre
    wph
    @0
    @32
    cc0
    cC
    etransclem14.c
    wph
    cM
    cc0
    cuz
    cfv
    #
    wcel
    cc0
    @0
    wcel
    wph
    cM
    cn0
    @33
    etransclem14.m
    nn0uz
    syl6eleq
    cc0
    cM
    eluzfz1
    syl
    ffvelrnd
    sseldi
    #
    wph
    @5
    @4
    cr
    etransclem14.cpm1
    @34
    eqeltrrd
    #
    lttri3d
    mpbid
    simprd
    iffalsed
    wph
    @10
    @7
    @11
    c1
    cmul
    wph
    @10
    @7
    c1
    cdiv
    co
    @7
    wph
    @9
    c1
    @7
    cdiv
    wph
    @9
    cc0
    cfa
    cfv
    c1
    wph
    @8
    cc0
    cfa
    wph
    @4
    @5
    wph
    @4
    @35
    recnd
    wph
    @5
    @4
    etransclem14.cpm1
    eqcomd
    subeq0bd
    #
    fveq2d
    fac0
    syl6eq
    oveq2d
    wph
    @7
    wph
    @7
    wph
    @4
    wph
    cP
    cn
    wcel
    @4
    cn0
    wcel
    etransclem14.n
    cP
    nnm1nn0
    syl
    faccld
    nncnd
    #
    div1d
    eqtrd
    wph
    @11
    cc0
    cc0
    cexp
    co
    c1
    wph
    cJ
    cc0
    @8
    cc0
    cexp
    etransclem14.j
    @36
    oveq12d
    0exp0e1
    syl6eq
    oveq12d
    wph
    @7
    @37
    mulid1d
    3eqtrd
    wph
    @14
    @21
    @27
    vj
    wph
    @15
    @20
    @26
    cc0
    wph
    @19
    @25
    @17
    cmul
    wph
    @18
    @24
    @16
    cexp
    wph
    @18
    cc0
    @1
    cmin
    co
    @24
    wph
    cJ
    cc0
    @1
    cmin
    etransclem14.j
    oveq1d
    @1
    df-neg
    syl6eqr
    oveq1d
    oveq2d
    ifeq2d
    prodeq2ad
    oveq12d
    oveq2d
    syl5eq
end
