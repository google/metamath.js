include "cfv.mm"
include "cdm.mm"
include "cc0.mm"
include "cfz.mm"
include "co.mm"
include "cv.mm"
include "cdvn.mm"
include "cprod.mm"
include "csu.mm"
include "cz.mm"
include "cc.mm"
include "cmpt.mm"
include "wceq.mm"
include "a1i.mm"
include "fveq2.mm"
include "prodeq2ad.mm"
include "sumeq2ad.mm"
include "adantl.mm"
include "cfn.mm"
include "wcel.mm"
include "dmfi.mm"
include "syl.mm"
include "wa.mm"
include "fzfid.mm"
include "cr.mm"
include "cpr.mm"
include "ad2antrr.mm"
include "ccnfld.mm"
include "ctopn.mm"
include "crest.mm"
include "cn.mm"
include "cmin.mm"
include "c1.mm"
include "cif.mm"
include "cexp.mm"
include "etransclem5.mm"
include "eqtri.mm"
include "simpr.mm"
include "cn0.mm"
include "cmap.mm"
include "wf.mm"
include "ffvelrnda.mm"
include "elmapi.mm"
include "etransclem20.mm"
include "ffvelrnd.mm"
include "fprodcl.mm"
include "fsumcl.mm"
include "fvmptd.mm"
include "clt.mm"
include "wbr.mm"
include "cfa.mm"
include "cdiv.mm"
include "cmul.mm"
include "etransclem21.mm"
include "iftrue.mm"
include "0zd.mm"
include "eqeltrd.mm"
include "wn.mm"
include "w3a.mm"
include "cle.mm"
include "nnm1nn0.mm"
include "nnnn0d.mm"
include "ifcld.mm"
include "nn0zd.mm"
include "ad3antrrr.mm"
include "adantr.mm"
include "zsubcld.mm"
include "3jca.mm"
include "zred.mm"
include "nltled.mm"
include "subge0d.mm"
include "mpbird.mm"
include "0red.mm"
include "nn0red.mm"
include "nn0ge0d.mm"
include "lesub2dd.mm"
include "recnd.mm"
include "subid1d.mm"
include "breqtrd.mm"
include "jca32.mm"
include "elfz2.mm"
include "sylibr.mm"
include "permnn.mm"
include "nnzd.mm"
include "elfzelz.mm"
include "ad2antlr.mm"
include "elnn0z.mm"
include "sylanbrc.mm"
include "zexpcl.mm"
include "syl2anc.mm"
include "zmulcld.mm"
include "pm2.61dan.mm"
include "fprodzcl.mm"
include "fsumzcl.mm"

theorem etransclem27
  let wph: wff ph
  let vx: setvar x
  let cC: class C
  let cP: class P
  let cS: class S
  let vj: setvar j
  let cG: class G
  let cH: class H
  let cJ: class J
  let cM: class M
  let cX: class X
  let vl: setvar l
  let vy: setvar y
  let vz: setvar z
  let vk: setvar k
  assume etransclem27.s: |- ( ph -> S e. { RR , CC } )
  assume etransclem27.x: |- ( ph -> X e. ( ( TopOpen ` CCfld ) |`t S ) )
  assume etransclem27.p: |- ( ph -> P e. NN )
  assume etransclem27.h: |- H = ( j e. ( 0 ... M ) |-> ( x e. X |-> ( ( x - j ) ^ if ( j = 0 , ( P - 1 ) , P ) ) ) )
  assume etransclem27.cfi: |- ( ph -> C e. Fin )
  assume etransclem27.cf: |- ( ph -> C : dom C --> ( NN0 ^m ( 0 ... M ) ) )
  assume etransclem27.g: |- G = ( x e. X |-> sum_ l e. dom C prod_ j e. ( 0 ... M ) ( ( ( S Dn ( H ` j ) ) ` ( ( C ` l ) ` j ) ) ` x ) )
  assume etransclem27.jx: |- ( ph -> J e. X )
  assume etransclem27.jz: |- ( ph -> J e. ZZ )

  disjoint C j
  disjoint C l
  disjoint C x
  disjoint j l
  disjoint j x
  disjoint l x
  disjoint H x
  disjoint J j
  disjoint J l
  disjoint J x
  disjoint M j
  disjoint M x
  disjoint P j
  disjoint P x
  disjoint S x
  disjoint X j
  disjoint X x
  disjoint j ph
  disjoint l ph
  disjoint ph x
  disjoint C y
  disjoint C z
  disjoint j y
  disjoint j z
  disjoint l y
  disjoint l z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint J y
  disjoint M y
  disjoint M z
  disjoint P y
  disjoint P z
  disjoint S y
  disjoint X y
  disjoint X z
  disjoint ph y
  disjoint ph z
  disjoint k x
  assert |- ( ph -> ( G ` J ) e. ZZ )

  proof
    wph
    cJ
    cG
    cfv
    cC
    cdm
    #
    cc0
    cM
    cfz
    co
    #
    cJ
    vj
    cv
    #
    vl
    cv
    #
    cC
    cfv
    #
    cfv
    #
    cS
    @2
    cH
    cfv
    cdvn
    co
    cfv
    #
    cfv
    #
    vj
    cprod
    #
    vl
    csu
    #
    cz
    wph
    vx
    cJ
    @0
    @1
    vx
    cv
    #
    @6
    cfv
    #
    vj
    cprod
    #
    vl
    csu
    #
    @9
    cX
    cG
    cc
    cG
    vx
    cX
    @13
    cmpt
    wceq
    wph
    etransclem27.g
    a1i
    @10
    cJ
    wceq
    #
    @13
    @9
    wceq
    wph
    @14
    @0
    @12
    @8
    vl
    @14
    @1
    @11
    @7
    vj
    @10
    cJ
    @6
    fveq2
    prodeq2ad
    sumeq2ad
    adantl
    etransclem27.jx
    wph
    @0
    @8
    vl
    wph
    cC
    cfn
    wcel
    @0
    cfn
    wcel
    etransclem27.cfi
    cC
    dmfi
    syl
    #
    wph
    @3
    @0
    wcel
    #
    wa
    #
    @1
    @7
    vj
    @17
    cc0
    cM
    fzfid
    #
    @17
    @2
    @1
    wcel
    #
    wa
    #
    cX
    cc
    cJ
    @6
    @20
    vy
    cP
    cS
    vz
    cH
    @2
    cM
    @5
    cX
    wph
    cS
    cr
    cc
    cpr
    wcel
    @16
    @19
    etransclem27.s
    ad2antrr
    #
    wph
    cX
    ccnfld
    ctopn
    cfv
    cS
    crest
    co
    wcel
    @16
    @19
    etransclem27.x
    ad2antrr
    #
    wph
    cP
    cn
    wcel
    #
    @16
    @19
    etransclem27.p
    ad2antrr
    #
    cH
    vj
    @1
    vx
    cX
    @10
    @2
    cmin
    co
    @2
    cc0
    wceq
    #
    cP
    c1
    cmin
    co
    #
    cP
    cif
    #
    cexp
    co
    cmpt
    cmpt
    vz
    @1
    vy
    cX
    vy
    cv
    vz
    cv
    #
    cmin
    co
    @28
    cc0
    wceq
    @26
    cP
    cif
    cexp
    co
    cmpt
    cmpt
    etransclem27.h
    vx
    vy
    cP
    vj
    vz
    cM
    cX
    etransclem5
    eqtri
    #
    @17
    @19
    simpr
    #
    @17
    @1
    cn0
    @2
    @4
    @17
    @4
    cn0
    @1
    cmap
    co
    #
    wcel
    @1
    cn0
    @4
    wf
    wph
    @0
    @31
    @3
    cC
    etransclem27.cf
    ffvelrnda
    @4
    cn0
    @1
    elmapi
    syl
    ffvelrnda
    #
    etransclem20
    wph
    cJ
    cX
    wcel
    @16
    @19
    etransclem27.jx
    ad2antrr
    #
    ffvelrnd
    fprodcl
    fsumcl
    fvmptd
    wph
    @0
    @8
    vl
    @15
    @17
    @1
    @7
    vj
    @18
    @20
    @7
    @27
    @5
    clt
    wbr
    #
    cc0
    @27
    cfa
    cfv
    @27
    @5
    cmin
    co
    #
    cfa
    cfv
    cdiv
    co
    #
    cJ
    @2
    cmin
    co
    #
    @35
    cexp
    co
    #
    cmul
    co
    #
    cif
    #
    cz
    @20
    vy
    cP
    cS
    vz
    cH
    @2
    cM
    @5
    cX
    cJ
    @21
    @22
    @24
    @29
    @30
    @32
    @33
    etransclem21
    @20
    @34
    @40
    cz
    wcel
    #
    @34
    @41
    @20
    @34
    @40
    cc0
    cz
    @34
    cc0
    @39
    iftrue
    @34
    0zd
    eqeltrd
    adantl
    @20
    @34
    wn
    #
    wa
    #
    @34
    cc0
    @39
    cz
    @43
    0zd
    #
    @43
    @36
    @38
    @43
    @36
    @43
    @35
    cc0
    @27
    cfz
    co
    wcel
    #
    @36
    cn
    wcel
    @43
    cc0
    cz
    wcel
    #
    @27
    cz
    wcel
    #
    @35
    cz
    wcel
    #
    w3a
    #
    cc0
    @35
    cle
    wbr
    #
    @35
    @27
    cle
    wbr
    #
    wa
    wa
    @45
    @43
    @49
    @50
    @51
    @43
    @46
    @47
    @48
    @44
    wph
    @47
    @16
    @19
    @42
    wph
    @27
    wph
    @25
    @26
    cP
    cn0
    wph
    @23
    @26
    cn0
    wcel
    etransclem27.p
    cP
    nnm1nn0
    syl
    wph
    cP
    etransclem27.p
    nnnn0d
    ifcld
    #
    nn0zd
    ad3antrrr
    #
    @43
    @27
    @5
    @53
    @20
    @5
    cz
    wcel
    @42
    @20
    @5
    @32
    nn0zd
    adantr
    #
    zsubcld
    #
    3jca
    @43
    @50
    @5
    @27
    cle
    wbr
    @43
    @5
    @27
    @43
    @5
    @54
    zred
    #
    @43
    @27
    @53
    zred
    #
    @20
    @42
    simpr
    nltled
    @43
    @27
    @5
    @57
    @56
    subge0d
    mpbird
    #
    @20
    @51
    @42
    @20
    @35
    @27
    cc0
    cmin
    co
    @27
    cle
    @20
    cc0
    @5
    @27
    @20
    0red
    @20
    @5
    @32
    nn0red
    wph
    @27
    cr
    wcel
    @16
    @19
    wph
    @27
    @52
    nn0red
    ad2antrr
    #
    @20
    @5
    @32
    nn0ge0d
    lesub2dd
    @20
    @27
    @20
    @27
    @59
    recnd
    subid1d
    breqtrd
    adantr
    jca32
    @35
    cc0
    @27
    elfz2
    sylibr
    @35
    @27
    permnn
    syl
    nnzd
    @43
    @37
    cz
    wcel
    @35
    cn0
    wcel
    #
    @38
    cz
    wcel
    @43
    cJ
    @2
    wph
    cJ
    cz
    wcel
    @16
    @19
    @42
    etransclem27.jz
    ad3antrrr
    @19
    @2
    cz
    wcel
    @17
    @42
    @2
    cc0
    cM
    elfzelz
    ad2antlr
    zsubcld
    @43
    @48
    @50
    @60
    @55
    @58
    @35
    elnn0z
    sylanbrc
    @37
    @35
    zexpcl
    syl2anc
    zmulcld
    ifcld
    pm2.61dan
    eqeltrd
    fprodzcl
    fsumzcl
    eqeltrd
end
