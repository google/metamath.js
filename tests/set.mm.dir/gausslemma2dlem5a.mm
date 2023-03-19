include "c1.mm"
include "caddc.mm"
include "co.mm"
include "cfz.mm"
include "cv.mm"
include "cfv.mm"
include "cprod.mm"
include "cmo.mm"
include "c2.mm"
include "cmul.mm"
include "cmin.mm"
include "cneg.mm"
include "wceq.mm"
include "wral.mm"
include "gausslemma2dlem3.mm"
include "prodeq2.mm"
include "oveq1d.mm"
include "syl.mm"
include "cprime.mm"
include "csn.mm"
include "cdif.mm"
include "wcel.mm"
include "eldifi.mm"
include "fzfid.mm"
include "wa.mm"
include "cz.mm"
include "prmz.mm"
include "adantr.mm"
include "elfzelz.mm"
include "2z.mm"
include "a1i.mm"
include "zmulcld.mm"
include "adantl.mm"
include "zsubcld.mm"
include "neg1z.mm"
include "prmnn.mm"
include "zcnd.mm"
include "mulm1d.mm"
include "cr.mm"
include "crp.mm"
include "zred.mm"
include "nnrpd.mm"
include "negmod.mm"
include "syl2anr.mm"
include "eqtr2d.mm"
include "fprodmodd.mm"
include "3syl.mm"
include "eqtrd.mm"

theorem gausslemma2dlem5a
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
  assert |- ( ph -> ( prod_ k e. ( ( M + 1 ) ... H ) ( R ` k ) mod P ) = ( prod_ k e. ( ( M + 1 ) ... H ) ( -u 1 x. ( k x. 2 ) ) mod P ) )

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
    #
    vk
    cprod
    #
    cP
    cmo
    co
    #
    @1
    cP
    @2
    c2
    cmul
    co
    #
    cmin
    co
    #
    vk
    cprod
    #
    cP
    cmo
    co
    #
    @1
    c1
    cneg
    #
    @6
    cmul
    co
    #
    vk
    cprod
    cP
    cmo
    co
    #
    wph
    @3
    @7
    wceq
    vk
    @1
    wral
    #
    @5
    @9
    wceq
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
    gausslemma2dlem3
    @13
    @4
    @8
    cP
    cmo
    @1
    @3
    @7
    vk
    prodeq2
    oveq1d
    syl
    wph
    cP
    cprime
    c2
    csn
    #
    cdif
    wcel
    cP
    cprime
    wcel
    #
    @9
    @12
    wceq
    gausslemma2d.p
    cP
    cprime
    @14
    eldifi
    @15
    @1
    @7
    @11
    vk
    cP
    @15
    @0
    cH
    fzfid
    @15
    @2
    @1
    wcel
    #
    wa
    #
    cP
    @6
    @15
    cP
    cz
    wcel
    @16
    cP
    prmz
    adantr
    @16
    @6
    cz
    wcel
    @15
    @16
    @2
    c2
    @2
    @0
    cH
    elfzelz
    c2
    cz
    wcel
    @16
    2z
    a1i
    zmulcld
    #
    adantl
    zsubcld
    @16
    @11
    cz
    wcel
    @15
    @16
    @10
    @6
    @10
    cz
    wcel
    @16
    neg1z
    a1i
    @18
    zmulcld
    adantl
    cP
    prmnn
    #
    @17
    @11
    cP
    cmo
    co
    @6
    cneg
    #
    cP
    cmo
    co
    #
    @7
    cP
    cmo
    co
    #
    @17
    @11
    @20
    cP
    cmo
    @16
    @11
    @20
    wceq
    @15
    @16
    @6
    @16
    @6
    @18
    zcnd
    mulm1d
    adantl
    oveq1d
    @16
    @6
    cr
    wcel
    cP
    crp
    wcel
    @21
    @22
    wceq
    @15
    @16
    @6
    @18
    zred
    @15
    cP
    @19
    nnrpd
    @6
    cP
    negmod
    syl2anr
    eqtr2d
    fprodmodd
    3syl
    eqtrd
end
