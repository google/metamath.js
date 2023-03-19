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
include "wceq.mm"
include "a1i.mm"
include "iftrue.mm"
include "adantl.mm"
include "wn.mm"
include "wa.mm"
include "iffalse.mm"
include "oveq1d.mm"
include "adantr.mm"
include "cz.mm"
include "wcel.mm"
include "cn.mm"
include "nnzd.mm"
include "1zzd.mm"
include "zsubcld.mm"
include "cuz.mm"
include "cn0.mm"
include "nn0uz.mm"
include "syl6eleq.mm"
include "eluzfz1.mm"
include "syl.mm"
include "ffvelrnd.mm"
include "elfzelzd.mm"
include "cr.mm"
include "zred.mm"
include "simpr.mm"
include "nltled.mm"
include "wne.mm"
include "necomd.mm"
include "leneltd.mm"
include "posdifd.mm"
include "mpbid.mm"
include "elnnz.mm"
include "sylanbrc.mm"
include "0expd.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "cc.mm"
include "nnm1nn0.mm"
include "faccld.mm"
include "nncnd.mm"
include "nnnn0d.mm"
include "nnne0d.mm"
include "divcld.mm"
include "mul01d.mm"
include "3eqtrd.mm"
include "pm2.61dan.mm"
include "eqeltrd.mm"
include "etransclem7.mm"
include "zcnd.mm"
include "mul02d.mm"
include "fzfid.mm"
include "fzssnn0.mm"
include "ffvelrnda.mm"
include "sseldi.mm"
include "fprodcl.mm"
include "fprodn0.mm"

theorem etransclem15
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
  assume etransclem15.p: |- ( ph -> P e. NN )
  assume etransclem15.m: |- ( ph -> M e. NN0 )
  assume etransclem15.n: |- ( ph -> N e. NN0 )
  assume etransclem15.c: |- ( ph -> C : ( 0 ... M ) --> ( 0 ... N ) )
  assume etransclem15.t: |- T = ( ( ( ! ` N ) / prod_ j e. ( 0 ... M ) ( ! ` ( C ` j ) ) ) x. ( if ( ( P - 1 ) < ( C ` 0 ) , 0 , ( ( ( ! ` ( P - 1 ) ) / ( ! ` ( ( P - 1 ) - ( C ` 0 ) ) ) ) x. ( J ^ ( ( P - 1 ) - ( C ` 0 ) ) ) ) ) x. prod_ j e. ( 1 ... M ) if ( P < ( C ` j ) , 0 , ( ( ( ! ` P ) / ( ! ` ( P - ( C ` j ) ) ) ) x. ( ( J - j ) ^ ( P - ( C ` j ) ) ) ) ) ) )
  assume etransclem15.j: |- ( ph -> J = 0 )
  assume etransclem15.cpm1: |- ( ph -> ( C ` 0 ) =/= ( P - 1 ) )

  disjoint M j
  disjoint j ph
  disjoint k x
  assert |- ( ph -> T = 0 )

  proof
    wph
    cT
    cN
    cfa
    cfv
    #
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
    #
    vj
    cprod
    #
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
    @7
    cfa
    cfv
    #
    @7
    @8
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
    @11
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
    cP
    @3
    clt
    wbr
    cc0
    cP
    cfa
    cfv
    cP
    @3
    cmin
    co
    #
    cfa
    cfv
    cdiv
    co
    cJ
    @2
    cmin
    co
    @17
    cexp
    co
    cmul
    co
    cif
    vj
    cprod
    #
    cmul
    co
    #
    cmul
    co
    #
    @6
    cc0
    cmul
    co
    cc0
    cT
    @20
    wceq
    wph
    etransclem15.t
    a1i
    wph
    @19
    cc0
    @6
    cmul
    wph
    @19
    cc0
    @18
    cmul
    co
    cc0
    wph
    @16
    cc0
    @18
    cmul
    wph
    @9
    @16
    cc0
    wceq
    #
    @9
    @21
    wph
    @9
    cc0
    @15
    iftrue
    adantl
    wph
    @9
    wn
    #
    wa
    #
    @16
    @15
    @13
    cc0
    cmul
    co
    cc0
    @22
    @16
    @15
    wceq
    wph
    @9
    cc0
    @15
    iffalse
    adantl
    @23
    @14
    cc0
    @13
    cmul
    @23
    @14
    cc0
    @11
    cexp
    co
    #
    cc0
    wph
    @14
    @24
    wceq
    @22
    wph
    cJ
    cc0
    @11
    cexp
    etransclem15.j
    oveq1d
    adantr
    @23
    @11
    @23
    @11
    cz
    wcel
    #
    cc0
    @11
    clt
    wbr
    #
    @11
    cn
    wcel
    wph
    @25
    @22
    wph
    @7
    @8
    wph
    cP
    c1
    wph
    cP
    etransclem15.p
    nnzd
    wph
    1zzd
    zsubcld
    #
    wph
    @8
    cc0
    cN
    wph
    @1
    cc0
    cN
    cfz
    co
    #
    cc0
    cC
    etransclem15.c
    wph
    cM
    cc0
    cuz
    cfv
    #
    wcel
    cc0
    @1
    wcel
    wph
    cM
    cn0
    @29
    etransclem15.m
    nn0uz
    syl6eleq
    cc0
    cM
    eluzfz1
    syl
    #
    ffvelrnd
    elfzelzd
    #
    zsubcld
    adantr
    @23
    @8
    @7
    clt
    wbr
    @26
    @23
    @8
    @7
    wph
    @8
    cr
    wcel
    @22
    wph
    @8
    @31
    zred
    adantr
    #
    wph
    @7
    cr
    wcel
    @22
    wph
    @7
    @27
    zred
    adantr
    #
    @23
    @8
    @7
    @32
    @33
    wph
    @22
    simpr
    nltled
    wph
    @7
    @8
    wne
    @22
    wph
    @8
    @7
    etransclem15.cpm1
    necomd
    adantr
    leneltd
    @23
    @8
    @7
    @32
    @33
    posdifd
    mpbid
    @11
    elnnz
    sylanbrc
    #
    0expd
    eqtrd
    oveq2d
    @23
    @13
    @23
    @10
    @12
    wph
    @10
    cc
    wcel
    @22
    wph
    @10
    wph
    @7
    wph
    cP
    cn
    wcel
    @7
    cn0
    wcel
    etransclem15.p
    cP
    nnm1nn0
    syl
    faccld
    nncnd
    adantr
    @23
    @12
    @23
    @11
    @23
    @11
    @34
    nnnn0d
    faccld
    #
    nncnd
    @23
    @12
    @35
    nnne0d
    divcld
    mul01d
    3eqtrd
    pm2.61dan
    oveq1d
    wph
    @18
    wph
    @18
    wph
    cC
    cP
    vj
    cJ
    cM
    cN
    etransclem15.p
    etransclem15.c
    wph
    cJ
    cc0
    @1
    etransclem15.j
    @30
    eqeltrd
    etransclem7
    zcnd
    mul02d
    eqtrd
    oveq2d
    wph
    @6
    wph
    @0
    @5
    wph
    @0
    wph
    cN
    etransclem15.n
    faccld
    nncnd
    wph
    @1
    @4
    vj
    wph
    cc0
    cM
    fzfid
    #
    wph
    @2
    @1
    wcel
    wa
    #
    @4
    @37
    @3
    @37
    @28
    cn0
    @3
    cN
    fzssnn0
    wph
    @1
    @28
    @2
    cC
    etransclem15.c
    ffvelrnda
    sseldi
    faccld
    #
    nncnd
    #
    fprodcl
    wph
    @1
    @4
    vj
    @36
    @39
    @37
    @4
    @38
    nnne0d
    fprodn0
    divcld
    mul01d
    3eqtrd
end
