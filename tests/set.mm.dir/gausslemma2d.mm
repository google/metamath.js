include "c1.mm"
include "cneg.mm"
include "cexp.mm"
include "co.mm"
include "c2.mm"
include "cmul.mm"
include "cmo.mm"
include "wceq.mm"
include "clgs.mm"
include "gausslemma2dlem7.mm"
include "cr.mm"
include "wcel.mm"
include "clt.mm"
include "wbr.mm"
include "wa.mm"
include "cprime.mm"
include "csn.mm"
include "cdif.mm"
include "eldifi.mm"
include "prmnn.mm"
include "nnred.mm"
include "prmgt1.mm"
include "jca.mm"
include "3syl.mm"
include "1mod.mm"
include "syl.mm"
include "eqcomd.mm"
include "eqeq2d.mm"
include "cz.mm"
include "crp.mm"
include "cn0.mm"
include "neg1z.mm"
include "gausslemma2dlem0h.mm"
include "zexpcl.mm"
include "sylancr.mm"
include "cn.mm"
include "2nn.mm"
include "a1i.mm"
include "gausslemma2dlem0b.mm"
include "nnnn0d.mm"
include "nnexpcld.mm"
include "nnzd.mm"
include "zmulcld.mm"
include "zred.mm"
include "1red.mm"
include "adantr.mm"
include "gausslemma2dlem0a.mm"
include "nnrpd.mm"
include "simpr.mm"
include "modmul1.mm"
include "syl3anc.mm"
include "ex.mm"
include "zcnd.mm"
include "nncnd.mm"
include "mul32d.mm"
include "caddc.mm"
include "nn0cnd.mm"
include "2timesd.mm"
include "oveq2d.mm"
include "cc.mm"
include "neg1cn.mm"
include "expaddd.mm"
include "nn0zd.mm"
include "m1expeven.mm"
include "3eqtr3d.mm"
include "oveq1d.mm"
include "mulid2d.mm"
include "3eqtrd.mm"
include "eqeq12d.mm"
include "cmin.mm"
include "cdiv.mm"
include "oveq2i.mm"
include "oveq1i.mm"
include "eqeq1i.mm"
include "2z.mm"
include "lgsvalmod.mm"
include "eqeq1d.mm"
include "gausslemma2dlem0i.mm"
include "sylbid.mm"
include "syl5bi.mm"
include "syld.mm"
include "mpd.mm"

theorem gausslemma2d
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
  assert |- ( ph -> ( 2 /L P ) = ( -u 1 ^ N ) )

  proof
    wph
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
    cP
    cmo
    co
    #
    c1
    wceq
    #
    c2
    cP
    clgs
    co
    #
    @1
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
    gausslemma2dlem7
    wph
    @5
    @4
    c1
    cP
    cmo
    co
    #
    wceq
    #
    @7
    wph
    c1
    @8
    @4
    wph
    @8
    c1
    wph
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
    @8
    c1
    wceq
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
    @12
    gausslemma2d.p
    cP
    cprime
    @13
    eldifi
    @15
    @10
    @11
    @15
    cP
    cP
    prmnn
    nnred
    cP
    prmgt1
    jca
    3syl
    cP
    1mod
    syl
    eqcomd
    eqeq2d
    wph
    @9
    @3
    @1
    cmul
    co
    #
    cP
    cmo
    co
    #
    c1
    @1
    cmul
    co
    #
    cP
    cmo
    co
    #
    wceq
    #
    @7
    wph
    @9
    @20
    wph
    @9
    wa
    @3
    cr
    wcel
    #
    c1
    cr
    wcel
    #
    wa
    #
    @1
    cz
    wcel
    #
    cP
    crp
    wcel
    #
    wa
    #
    @9
    @20
    wph
    @23
    @9
    wph
    @21
    @22
    wph
    @3
    wph
    @1
    @2
    wph
    @0
    cz
    wcel
    cN
    cn0
    wcel
    @24
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
    #
    @0
    cN
    zexpcl
    sylancr
    #
    wph
    @2
    wph
    c2
    cH
    c2
    cn
    wcel
    wph
    2nn
    a1i
    wph
    cH
    wph
    cP
    cH
    gausslemma2d.p
    gausslemma2d.h
    gausslemma2dlem0b
    nnnn0d
    nnexpcld
    #
    nnzd
    zmulcld
    zred
    wph
    1red
    jca
    adantr
    wph
    @26
    @9
    wph
    @24
    @25
    @28
    wph
    cP
    wph
    cP
    gausslemma2d.p
    gausslemma2dlem0a
    nnrpd
    jca
    adantr
    wph
    @9
    simpr
    @3
    c1
    @1
    cP
    modmul1
    syl3anc
    ex
    wph
    @20
    @2
    cP
    cmo
    co
    #
    @1
    cP
    cmo
    co
    #
    wceq
    #
    @7
    wph
    @17
    @30
    @19
    @31
    wph
    @16
    @2
    cP
    cmo
    wph
    @16
    @1
    @1
    cmul
    co
    #
    @2
    cmul
    co
    c1
    @2
    cmul
    co
    @2
    wph
    @1
    @2
    @1
    wph
    @1
    @28
    zcnd
    #
    wph
    @2
    @29
    nncnd
    #
    @34
    mul32d
    wph
    @33
    c1
    @2
    cmul
    wph
    @0
    cN
    cN
    caddc
    co
    #
    cexp
    co
    @0
    c2
    cN
    cmul
    co
    #
    cexp
    co
    #
    @33
    c1
    wph
    @36
    @37
    @0
    cexp
    wph
    @37
    @36
    wph
    cN
    wph
    cN
    @27
    nn0cnd
    2timesd
    eqcomd
    oveq2d
    wph
    @0
    cN
    cN
    @0
    cc
    wcel
    wph
    neg1cn
    a1i
    @27
    @27
    expaddd
    wph
    cN
    cz
    wcel
    @38
    c1
    wceq
    wph
    cN
    @27
    nn0zd
    cN
    m1expeven
    syl
    3eqtr3d
    oveq1d
    wph
    @2
    @35
    mulid2d
    3eqtrd
    oveq1d
    wph
    @18
    @1
    cP
    cmo
    wph
    @1
    @34
    mulid2d
    oveq1d
    eqeq12d
    @32
    c2
    cP
    c1
    cmin
    co
    c2
    cdiv
    co
    #
    cexp
    co
    #
    cP
    cmo
    co
    #
    @31
    wceq
    #
    wph
    @7
    @30
    @41
    @31
    @2
    @40
    cP
    cmo
    cH
    @39
    c2
    cexp
    gausslemma2d.h
    oveq2i
    oveq1i
    eqeq1i
    wph
    @42
    @6
    cP
    cmo
    co
    #
    @31
    wceq
    @7
    wph
    @41
    @43
    @31
    wph
    @43
    @41
    wph
    c2
    cz
    wcel
    @14
    @43
    @41
    wceq
    2z
    gausslemma2d.p
    c2
    cP
    lgsvalmod
    sylancr
    eqcomd
    eqeq1d
    wph
    cP
    cH
    cM
    cN
    gausslemma2d.p
    gausslemma2d.m
    gausslemma2d.h
    gausslemma2d.n
    gausslemma2dlem0i
    sylbid
    syl5bi
    sylbid
    syld
    sylbid
    mpd
end
