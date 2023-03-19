include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfz.mm"
include "cv.mm"
include "cfv.mm"
include "cprod.mm"
include "cmo.mm"
include "cneg.mm"
include "c2.mm"
include "cmul.mm"
include "cexp.mm"
include "gausslemma2dlem5a.mm"
include "cfn.mm"
include "wcel.mm"
include "fzfi.mm"
include "a1i.mm"
include "cc.mm"
include "wa.mm"
include "neg1cn.mm"
include "elfzelz.mm"
include "cz.mm"
include "2z.mm"
include "zmulcld.mm"
include "zcnd.mm"
include "adantl.mm"
include "fprodmul.mm"
include "chash.mm"
include "wceq.mm"
include "pm3.2i.mm"
include "fprodconst.mm"
include "mp1i.mm"
include "cmin.mm"
include "cuz.mm"
include "cle.mm"
include "wbr.mm"
include "c4.mm"
include "cdiv.mm"
include "cfl.mm"
include "cprime.mm"
include "csn.mm"
include "cdif.mm"
include "cn.mm"
include "cdvds.mm"
include "wn.mm"
include "cr.mm"
include "nnoddn2prm.mm"
include "nnre.mm"
include "adantr.mm"
include "3syl.mm"
include "4re.mm"
include "cc0.mm"
include "wne.mm"
include "4ne0.mm"
include "redivcld.mm"
include "flcld.mm"
include "syl5eqel.mm"
include "peano2zd.mm"
include "wb.mm"
include "nnz.mm"
include "oddm1d2.mm"
include "syl.mm"
include "biimpa.mm"
include "gausslemma2dlem0f.mm"
include "eluz2.mm"
include "syl3anbrc.mm"
include "hashfz.mm"
include "1cnd.mm"
include "nppcan2d.mm"
include "syl6eqr.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "oveq1d.mm"

theorem gausslemma2dlem5
  let wph: wff ph
  let vx: setvar x
  let cP: class P
  let cR: class R
  let vk: setvar k
  let cH: class H
  let cM: class M
  let cN: class N
  let vy: setvar y
  let vl: setvar l
  assume gausslemma2d.p: |- ( ph -> P e. ( Prime \ { 2 } ) )
  assume gausslemma2d.h: |- H = ( ( P - 1 ) / 2 )
  assume gausslemma2d.r: |- R = ( x e. ( 1 ... H ) |-> if ( ( x x. 2 ) < ( P / 2 ) , ( x x. 2 ) , ( P - ( x x. 2 ) ) ) )
  assume gausslemma2d.m: |- M = ( |_ ` ( P / 4 ) )
  assume gausslemma2d.n: |- N = ( H - M )

  disjoint H x
  disjoint P x
  disjoint ph x
  disjoint H k
  disjoint R k
  disjoint k ph
  disjoint M x
  disjoint k x
  disjoint M k
  disjoint P k
  disjoint H y
  disjoint x y
  disjoint R y
  disjoint ph y
  disjoint H l
  disjoint k l
  disjoint R l
  disjoint l ph
  assert |- ( ph -> ( prod_ k e. ( ( M + 1 ) ... H ) ( R ` k ) mod P ) = ( ( ( -u 1 ^ N ) x. prod_ k e. ( ( M + 1 ) ... H ) ( k x. 2 ) ) mod P ) )

  proof
    wph
    cM
    c1
    caddc
    co
    #
    cH
    cfz
    co
    #
    vk
    cv
    #
    cR
    cfv
    vk
    cprod
    cP
    cmo
    co
    @1
    c1
    cneg
    #
    @2
    c2
    cmul
    co
    #
    cmul
    co
    vk
    cprod
    #
    cP
    cmo
    co
    @3
    cN
    cexp
    co
    #
    @1
    @4
    vk
    cprod
    #
    cmul
    co
    #
    cP
    cmo
    co
    wph
    vx
    cP
    cR
    vk
    cH
    cM
    gausslemma2d.p
    gausslemma2d.h
    gausslemma2d.r
    gausslemma2d.m
    gausslemma2dlem5a
    wph
    @5
    @8
    cP
    cmo
    wph
    @5
    @1
    @3
    vk
    cprod
    #
    @7
    cmul
    co
    @8
    wph
    @1
    @3
    @4
    vk
    @1
    cfn
    wcel
    #
    wph
    @0
    cH
    fzfi
    #
    a1i
    @3
    cc
    wcel
    #
    wph
    @2
    @1
    wcel
    #
    wa
    neg1cn
    a1i
    @13
    @4
    cc
    wcel
    wph
    @13
    @4
    @13
    @2
    c2
    @2
    @0
    cH
    elfzelz
    c2
    cz
    wcel
    @13
    2z
    a1i
    zmulcld
    zcnd
    adantl
    fprodmul
    wph
    @9
    @6
    @7
    cmul
    wph
    @9
    @3
    @1
    chash
    cfv
    #
    cexp
    co
    #
    @6
    @10
    @12
    wa
    @9
    @15
    wceq
    wph
    @10
    @12
    @11
    neg1cn
    pm3.2i
    @1
    @3
    vk
    fprodconst
    mp1i
    wph
    @14
    cN
    @3
    cexp
    wph
    @14
    cH
    @0
    cmin
    co
    c1
    caddc
    co
    #
    cN
    wph
    cH
    @0
    cuz
    cfv
    wcel
    #
    @14
    @16
    wceq
    wph
    @0
    cz
    wcel
    cH
    cz
    wcel
    @0
    cH
    cle
    wbr
    @17
    wph
    cM
    wph
    cM
    cP
    c4
    cdiv
    co
    #
    cfl
    cfv
    cz
    gausslemma2d.m
    wph
    @18
    wph
    cP
    c4
    wph
    cP
    cprime
    c2
    csn
    cdif
    wcel
    #
    cP
    cn
    wcel
    #
    c2
    cP
    cdvds
    wbr
    wn
    #
    wa
    #
    cP
    cr
    wcel
    #
    gausslemma2d.p
    cP
    nnoddn2prm
    #
    @20
    @23
    @21
    cP
    nnre
    adantr
    3syl
    c4
    cr
    wcel
    wph
    4re
    a1i
    c4
    cc0
    wne
    wph
    4ne0
    a1i
    redivcld
    flcld
    syl5eqel
    #
    peano2zd
    wph
    cH
    cP
    c1
    cmin
    co
    c2
    cdiv
    co
    #
    cz
    gausslemma2d.h
    wph
    @19
    @22
    @26
    cz
    wcel
    #
    gausslemma2d.p
    @24
    @20
    @21
    @27
    @20
    cP
    cz
    wcel
    @21
    @27
    wb
    cP
    nnz
    cP
    oddm1d2
    syl
    biimpa
    3syl
    syl5eqel
    #
    wph
    cP
    cH
    cM
    gausslemma2d.p
    gausslemma2d.m
    gausslemma2d.h
    gausslemma2dlem0f
    @0
    cH
    eluz2
    syl3anbrc
    @0
    cH
    hashfz
    syl
    wph
    @16
    cH
    cM
    cmin
    co
    cN
    wph
    cH
    cM
    c1
    wph
    cH
    @28
    zcnd
    wph
    cM
    @25
    zcnd
    wph
    1cnd
    nppcan2d
    gausslemma2d.n
    syl6eqr
    eqtrd
    oveq2d
    eqtrd
    oveq1d
    eqtrd
    oveq1d
    eqtrd
end
