include "cfa.mm"
include "cfv.mm"
include "cmo.mm"
include "co.mm"
include "c1.mm"
include "cneg.mm"
include "cexp.mm"
include "c2.mm"
include "cmul.mm"
include "wceq.mm"
include "gausslemma2dlem6.mm"
include "gausslemma2dlem0b.mm"
include "nnnn0d.mm"
include "faccld.mm"
include "nncnd.mm"
include "mulid2d.mm"
include "eqcomd.mm"
include "oveq1d.mm"
include "eqeq1d.mm"
include "cz.mm"
include "wcel.mm"
include "cn.mm"
include "cgcd.mm"
include "wb.mm"
include "1zzd.mm"
include "cn0.mm"
include "neg1z.mm"
include "gausslemma2dlem0h.mm"
include "zexpcl.mm"
include "sylancr.mm"
include "2z.mm"
include "zmulcld.mm"
include "nnzd.mm"
include "cprime.mm"
include "csn.mm"
include "cdif.mm"
include "eldifi.mm"
include "prmnn.mm"
include "3syl.mm"
include "gausslemma2dlem0c.mm"
include "cncongrcoprm.mm"
include "syl32anc.mm"
include "bitrd.mm"
include "wa.mm"
include "simpr.mm"
include "cr.mm"
include "clt.mm"
include "wbr.mm"
include "nnred.mm"
include "prmgt1.mm"
include "jca.mm"
include "syl.mm"
include "1mod.mm"
include "adantr.mm"
include "eqtr3d.mm"
include "ex.mm"
include "sylbid.mm"
include "mpd.mm"

theorem gausslemma2dlem7
  let wph: wff ph
  let vx: setvar x
  let cP: class P
  let cR: class R
  let cH: class H
  let cM: class M
  let cN: class N
  let vy: setvar y
  let vk: setvar k
  let vl: setvar l
  assume gausslemma2d.p: |- ( ph -> P e. ( Prime \ { 2 } ) )
  assume gausslemma2d.h: |- H = ( ( P - 1 ) / 2 )
  assume gausslemma2d.r: |- R = ( x e. ( 1 ... H ) |-> if ( ( x x. 2 ) < ( P / 2 ) , ( x x. 2 ) , ( P - ( x x. 2 ) ) ) )
  assume gausslemma2d.m: |- M = ( |_ ` ( P / 4 ) )
  assume gausslemma2d.n: |- N = ( H - M )

  disjoint H x
  disjoint P x
  disjoint ph x
  disjoint M x
  disjoint H y
  disjoint x y
  disjoint R y
  disjoint ph y
  disjoint H k
  disjoint H l
  disjoint k l
  disjoint R k
  disjoint R l
  disjoint k ph
  disjoint l ph
  disjoint k x
  disjoint M k
  disjoint P k
  assert |- ( ph -> ( ( ( -u 1 ^ N ) x. ( 2 ^ H ) ) mod P ) = 1 )

  proof
    wph
    cH
    cfa
    cfv
    #
    cP
    cmo
    co
    #
    c1
    cneg
    #
    cN
    cexp
    co
    #
    c2
    cH
    cexp
    co
    #
    cmul
    co
    #
    @0
    cmul
    co
    cP
    cmo
    co
    #
    wceq
    #
    @5
    cP
    cmo
    co
    #
    c1
    wceq
    #
    wph
    vx
    cP
    cR
    cH
    cM
    cN
    gausslemma2d.p
    gausslemma2d.h
    gausslemma2d.r
    gausslemma2d.m
    gausslemma2d.n
    gausslemma2dlem6
    wph
    @7
    c1
    cP
    cmo
    co
    #
    @8
    wceq
    #
    @9
    wph
    @7
    c1
    @0
    cmul
    co
    #
    cP
    cmo
    co
    #
    @6
    wceq
    #
    @11
    wph
    @1
    @13
    @6
    wph
    @0
    @12
    cP
    cmo
    wph
    @12
    @0
    wph
    @0
    wph
    @0
    wph
    cH
    wph
    cH
    wph
    cP
    cH
    gausslemma2d.p
    gausslemma2d.h
    gausslemma2dlem0b
    nnnn0d
    #
    faccld
    #
    nncnd
    mulid2d
    eqcomd
    oveq1d
    eqeq1d
    wph
    c1
    cz
    wcel
    @5
    cz
    wcel
    @0
    cz
    wcel
    cP
    cn
    wcel
    #
    @0
    cP
    cgcd
    co
    c1
    wceq
    @14
    @11
    wb
    wph
    1zzd
    wph
    @3
    @4
    wph
    @2
    cz
    wcel
    cN
    cn0
    wcel
    @3
    cz
    wcel
    neg1z
    wph
    cP
    cH
    cM
    cN
    gausslemma2d.p
    gausslemma2d.m
    gausslemma2d.h
    gausslemma2d.n
    gausslemma2dlem0h
    @2
    cN
    zexpcl
    sylancr
    wph
    c2
    cz
    wcel
    cH
    cn0
    wcel
    @4
    cz
    wcel
    2z
    @15
    c2
    cH
    zexpcl
    sylancr
    zmulcld
    wph
    @0
    @16
    nnzd
    wph
    cP
    cprime
    c2
    csn
    #
    cdif
    wcel
    #
    cP
    cprime
    wcel
    #
    @17
    gausslemma2d.p
    cP
    cprime
    @18
    eldifi
    #
    cP
    prmnn
    #
    3syl
    wph
    cP
    cH
    gausslemma2d.p
    gausslemma2d.h
    gausslemma2dlem0c
    c1
    @5
    @0
    cP
    cncongrcoprm
    syl32anc
    bitrd
    wph
    @11
    @9
    wph
    @11
    wa
    @10
    @8
    c1
    wph
    @11
    simpr
    wph
    @10
    c1
    wceq
    #
    @11
    wph
    @19
    cP
    cr
    wcel
    #
    c1
    cP
    clt
    wbr
    #
    wa
    #
    @23
    gausslemma2d.p
    @19
    @20
    @26
    @21
    @20
    @24
    @25
    @20
    cP
    @22
    nnred
    cP
    prmgt1
    jca
    syl
    cP
    1mod
    3syl
    adantr
    eqtr3d
    ex
    sylbid
    mpd
end
