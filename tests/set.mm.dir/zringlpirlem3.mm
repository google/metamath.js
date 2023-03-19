include "cdvds.mm"
include "wbr.mm"
include "cmo.mm"
include "co.mm"
include "cc0.mm"
include "wceq.mm"
include "cn.mm"
include "wcel.mm"
include "wn.mm"
include "wo.mm"
include "cle.mm"
include "clt.mm"
include "cr.mm"
include "crp.mm"
include "cz.mm"
include "zring.mm"
include "clidl.mm"
include "cfv.mm"
include "wss.mm"
include "zringbas.mm"
include "eqid.mm"
include "lidlss.mm"
include "syl.mm"
include "sseldd.mm"
include "zred.mm"
include "cin.mm"
include "inss2.mm"
include "cinf.mm"
include "c1.mm"
include "cuz.mm"
include "c0.mm"
include "wne.mm"
include "nnuz.mm"
include "sseqtri.mm"
include "zringlpirlem1.mm"
include "infssuzcl.mm"
include "sylancr.mm"
include "syl5eqel.mm"
include "sseldi.mm"
include "nnrpd.mm"
include "modlt.mm"
include "syl2anc.mm"
include "zmodcld.mm"
include "nn0red.mm"
include "nnred.mm"
include "ltnled.mm"
include "mpbid.mm"
include "wa.mm"
include "cdiv.mm"
include "cfl.mm"
include "cneg.mm"
include "cmul.mm"
include "caddc.mm"
include "cmin.mm"
include "zcnd.mm"
include "nncnd.mm"
include "nndivred.mm"
include "flcld.mm"
include "mulcld.mm"
include "negsubd.mm"
include "znegcld.mm"
include "mulcomd.mm"
include "mulneg2d.mm"
include "eqtrd.mm"
include "oveq2d.mm"
include "modval.mm"
include "3eqtr4rd.mm"
include "crg.mm"
include "zringring.mm"
include "a1i.mm"
include "zringlpirlem2.mm"
include "zringmulr.mm"
include "lidlmcl.mm"
include "syl22anc.mm"
include "zringplusg.mm"
include "lidlacl.mm"
include "eqeltrd.mm"
include "adantr.mm"
include "simpr.mm"
include "elind.mm"
include "infssuzle.mm"
include "syl5eqbr.mm"
include "mtand.mm"
include "cn0.mm"
include "elnn0.mm"
include "sylib.mm"
include "orel1.mm"
include "sylc.mm"
include "wb.mm"
include "dvdsval3.mm"
include "mpbird.mm"

theorem zringlpirlem3
  let wph: wff ph
  let cG: class G
  let cI: class I
  let cX: class X
  let va: setvar a
  assume zringlpirlem.i: |- ( ph -> I e. ( LIdeal ` ZZring ) )
  assume zringlpirlem.n0: |- ( ph -> I =/= { 0 } )
  assume zringlpirlem.g: |- G = inf ( ( I i^i NN ) , RR , < )
  assume zringlpirlem.x: |- ( ph -> X e. I )


  assert |- ( ph -> G || X )

  proof
    wph
    cG
    cX
    cdvds
    wbr
    #
    cX
    cG
    cmo
    co
    #
    cc0
    wceq
    #
    wph
    @1
    cn
    wcel
    #
    wn
    @3
    @2
    wo
    #
    @2
    wph
    @3
    cG
    @1
    cle
    wbr
    #
    wph
    @1
    cG
    clt
    wbr
    #
    @5
    wn
    wph
    cX
    cr
    wcel
    #
    cG
    crp
    wcel
    #
    @6
    wph
    cX
    wph
    cI
    cz
    cX
    wph
    cI
    zring
    clidl
    cfv
    #
    wcel
    #
    cI
    cz
    wss
    zringlpirlem.i
    cz
    cI
    @9
    zring
    zringbas
    @9
    eqid
    #
    lidlss
    syl
    zringlpirlem.x
    sseldd
    #
    zred
    #
    wph
    cG
    wph
    cI
    cn
    cin
    #
    cn
    cG
    cI
    cn
    inss2
    #
    wph
    cG
    @14
    cr
    clt
    cinf
    #
    @14
    zringlpirlem.g
    wph
    @14
    c1
    cuz
    cfv
    #
    wss
    #
    @14
    c0
    wne
    @16
    @14
    wcel
    @14
    cn
    @17
    @15
    nnuz
    sseqtri
    #
    wph
    cI
    zringlpirlem.i
    zringlpirlem.n0
    zringlpirlem1
    @14
    c1
    infssuzcl
    sylancr
    syl5eqel
    sseldi
    #
    nnrpd
    #
    cX
    cG
    modlt
    syl2anc
    wph
    @1
    cG
    wph
    @1
    wph
    cX
    cG
    @12
    @20
    zmodcld
    #
    nn0red
    wph
    cG
    @20
    nnred
    ltnled
    mpbid
    wph
    @3
    wa
    #
    cG
    @16
    @1
    cle
    zringlpirlem.g
    @23
    @18
    @1
    @14
    wcel
    @16
    @1
    cle
    wbr
    @19
    @23
    cI
    cn
    @1
    wph
    @1
    cI
    wcel
    @3
    wph
    @1
    cX
    cX
    cG
    cdiv
    co
    #
    cfl
    cfv
    #
    cneg
    #
    cG
    cmul
    co
    #
    caddc
    co
    #
    cI
    wph
    cX
    cG
    @25
    cmul
    co
    #
    cneg
    #
    caddc
    co
    cX
    @29
    cmin
    co
    #
    @28
    @1
    wph
    cX
    @29
    wph
    cX
    @12
    zcnd
    wph
    cG
    @25
    wph
    cG
    @20
    nncnd
    #
    wph
    @25
    wph
    @24
    wph
    cX
    cG
    @13
    @20
    nndivred
    flcld
    #
    zcnd
    #
    mulcld
    negsubd
    wph
    @27
    @30
    cX
    caddc
    wph
    @27
    cG
    @26
    cmul
    co
    @30
    wph
    @26
    cG
    wph
    @26
    wph
    @25
    @33
    znegcld
    #
    zcnd
    @32
    mulcomd
    wph
    cG
    @25
    @32
    @34
    mulneg2d
    eqtrd
    oveq2d
    wph
    @7
    @8
    @1
    @31
    wceq
    @13
    @21
    cX
    cG
    modval
    syl2anc
    3eqtr4rd
    wph
    zring
    crg
    wcel
    #
    @10
    cX
    cI
    wcel
    @27
    cI
    wcel
    #
    @28
    cI
    wcel
    @36
    wph
    zringring
    a1i
    #
    zringlpirlem.i
    zringlpirlem.x
    wph
    @36
    @10
    @26
    cz
    wcel
    cG
    cI
    wcel
    @37
    @38
    zringlpirlem.i
    @35
    wph
    cG
    cI
    zringlpirlem.i
    zringlpirlem.n0
    zringlpirlem.g
    zringlpirlem2
    cz
    zring
    cmul
    @9
    cI
    @26
    cG
    @11
    zringbas
    zringmulr
    lidlmcl
    syl22anc
    caddc
    zring
    @9
    cI
    cX
    @27
    @11
    zringplusg
    lidlacl
    syl22anc
    eqeltrd
    adantr
    wph
    @3
    simpr
    elind
    @1
    @14
    c1
    infssuzle
    sylancr
    syl5eqbr
    mtand
    wph
    @1
    cn0
    wcel
    @4
    @22
    @1
    elnn0
    sylib
    @3
    @2
    orel1
    sylc
    wph
    cG
    cn
    wcel
    cX
    cz
    wcel
    @0
    @2
    wb
    @20
    @12
    cG
    cX
    dvdsval3
    syl2anc
    mpbird
end
