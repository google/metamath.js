include "caddc.mm"
include "co.mm"
include "citg.mm"
include "cr.mm"
include "cv.mm"
include "wcel.mm"
include "cc0.mm"
include "cif.mm"
include "cmpt.mm"
include "citg2.mm"
include "cfv.mm"
include "wa.mm"
include "readdcld.mm"
include "ibladdnc.mm"
include "addge0d.mm"
include "itgposval.mm"
include "cof.mm"
include "oveq12d.mm"
include "cpnf.mm"
include "cico.mm"
include "cvol.mm"
include "cdm.mm"
include "wss.mm"
include "cibl.mm"
include "cmbf.mm"
include "iblmbf.mm"
include "syl.mm"
include "mbfdm2.mm"
include "mblss.mm"
include "rembl.mm"
include "a1i.mm"
include "cle.mm"
include "wbr.mm"
include "elrege0.mm"
include "sylanbrc.mm"
include "wn.mm"
include "0e0icopnf.mm"
include "ifclda.mm"
include "adantr.mm"
include "cdif.mm"
include "wceq.mm"
include "eldifn.mm"
include "adantl.mm"
include "iffalse.mm"
include "iftrue.mm"
include "mpteq2ia.mm"
include "syl5eqel.mm"
include "mbfss.mm"
include "eqid.mm"
include "fmptd.mm"
include "iblpos.mm"
include "mpbid.mm"
include "simprd.mm"
include "itg2addnc.mm"
include "cvv.mm"
include "reex.mm"
include "eqidd.mm"
include "offval2.mm"
include "eqtr4d.mm"
include "00id.mm"
include "syl6eq.mm"
include "pm2.61i.mm"
include "mpteq2i.mm"
include "fveq2d.mm"
include "3eqtr2d.mm"

theorem itgaddnclem1
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  assume ibladdnc.1: |- ( ( ph /\ x e. A ) -> B e. V )
  assume ibladdnc.2: |- ( ph -> ( x e. A |-> B ) e. L^1 )
  assume ibladdnc.3: |- ( ( ph /\ x e. A ) -> C e. V )
  assume ibladdnc.4: |- ( ph -> ( x e. A |-> C ) e. L^1 )
  assume ibladdnc.m: |- ( ph -> ( x e. A |-> ( B + C ) ) e. MblFn )
  assume itgaddnclem.1: |- ( ( ph /\ x e. A ) -> B e. RR )
  assume itgaddnclem.2: |- ( ( ph /\ x e. A ) -> C e. RR )
  assume itgaddnclem.3: |- ( ( ph /\ x e. A ) -> 0 <_ B )
  assume itgaddnclem.4: |- ( ( ph /\ x e. A ) -> 0 <_ C )

  disjoint A x
  disjoint V x
  disjoint ph x
  assert |- ( ph -> S. A ( B + C ) _d x = ( S. A B _d x + S. A C _d x ) )

  proof
    wph
    vx
    cA
    cB
    cC
    caddc
    co
    #
    citg
    vx
    cr
    vx
    cv
    #
    cA
    wcel
    #
    @0
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    #
    vx
    cA
    cB
    citg
    #
    vx
    cA
    cC
    citg
    #
    caddc
    co
    #
    wph
    vx
    cA
    @0
    wph
    @2
    wa
    #
    cB
    cC
    itgaddnclem.1
    itgaddnclem.2
    readdcld
    wph
    vx
    cA
    cB
    cC
    cV
    ibladdnc.1
    ibladdnc.2
    ibladdnc.3
    ibladdnc.4
    ibladdnc.m
    ibladdnc
    @9
    cB
    cC
    itgaddnclem.1
    itgaddnclem.2
    itgaddnclem.3
    itgaddnclem.4
    addge0d
    itgposval
    wph
    @8
    vx
    cr
    @2
    cB
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    #
    vx
    cr
    @2
    cC
    cc0
    cif
    #
    cmpt
    #
    citg2
    cfv
    #
    caddc
    co
    @11
    @14
    caddc
    cof
    co
    #
    citg2
    cfv
    @5
    wph
    @6
    @12
    @7
    @15
    caddc
    wph
    vx
    cA
    cB
    itgaddnclem.1
    ibladdnc.2
    itgaddnclem.3
    itgposval
    wph
    vx
    cA
    cC
    itgaddnclem.2
    ibladdnc.4
    itgaddnclem.4
    itgposval
    oveq12d
    wph
    @11
    @14
    wph
    vx
    cA
    cr
    @10
    cc0
    cpnf
    cico
    co
    #
    wph
    cA
    cvol
    cdm
    #
    wcel
    cA
    cr
    wss
    wph
    vx
    cA
    cB
    cV
    wph
    vx
    cA
    cB
    cmpt
    #
    cibl
    wcel
    #
    @19
    cmbf
    wcel
    #
    ibladdnc.2
    @19
    iblmbf
    syl
    #
    ibladdnc.1
    mbfdm2
    cA
    mblss
    syl
    cr
    @18
    wcel
    wph
    rembl
    a1i
    wph
    @10
    @17
    wcel
    #
    @2
    wph
    @2
    cB
    cc0
    @17
    @9
    cB
    cr
    wcel
    cc0
    cB
    cle
    wbr
    cB
    @17
    wcel
    itgaddnclem.1
    itgaddnclem.3
    cB
    elrege0
    sylanbrc
    cc0
    @17
    wcel
    wph
    @2
    wn
    #
    wa
    0e0icopnf
    a1i
    #
    ifclda
    #
    adantr
    wph
    @1
    cr
    cA
    cdif
    wcel
    #
    wa
    @24
    @10
    cc0
    wceq
    @27
    @24
    wph
    @1
    cr
    cA
    eldifn
    adantl
    @2
    cB
    cc0
    iffalse
    #
    syl
    wph
    vx
    cA
    @10
    cmpt
    @19
    cmbf
    vx
    cA
    @10
    cB
    @2
    cB
    cc0
    iftrue
    #
    mpteq2ia
    @22
    syl5eqel
    mbfss
    wph
    vx
    cr
    @10
    @17
    @11
    wph
    @23
    @1
    cr
    wcel
    #
    @26
    adantr
    #
    @11
    eqid
    fmptd
    wph
    @21
    @12
    cr
    wcel
    #
    wph
    @20
    @21
    @32
    wa
    ibladdnc.2
    wph
    vx
    cA
    cB
    itgaddnclem.1
    itgaddnclem.3
    iblpos
    mpbid
    simprd
    wph
    vx
    cr
    @13
    @17
    @14
    wph
    @13
    @17
    wcel
    @30
    wph
    @2
    cC
    cc0
    @17
    @9
    cC
    cr
    wcel
    cc0
    cC
    cle
    wbr
    cC
    @17
    wcel
    itgaddnclem.2
    itgaddnclem.4
    cC
    elrege0
    sylanbrc
    @25
    ifclda
    adantr
    #
    @14
    eqid
    fmptd
    wph
    vx
    cA
    cC
    cmpt
    #
    cmbf
    wcel
    #
    @15
    cr
    wcel
    #
    wph
    @34
    cibl
    wcel
    @35
    @36
    wa
    ibladdnc.4
    wph
    vx
    cA
    cC
    itgaddnclem.2
    itgaddnclem.4
    iblpos
    mpbid
    simprd
    itg2addnc
    wph
    @16
    @4
    citg2
    wph
    @16
    vx
    cr
    @10
    @13
    caddc
    co
    #
    cmpt
    @4
    wph
    vx
    cr
    @10
    @13
    caddc
    @11
    @14
    cvv
    @17
    @17
    cr
    cvv
    wcel
    wph
    reex
    a1i
    @31
    @33
    wph
    @11
    eqidd
    wph
    @14
    eqidd
    offval2
    vx
    cr
    @37
    @3
    @2
    @37
    @3
    wceq
    @2
    @37
    @0
    @3
    @2
    @10
    cB
    @13
    cC
    caddc
    @29
    @2
    cC
    cc0
    iftrue
    oveq12d
    @2
    @0
    cc0
    iftrue
    eqtr4d
    @24
    @37
    cc0
    @3
    @24
    @37
    cc0
    cc0
    caddc
    co
    cc0
    @24
    @10
    cc0
    @13
    cc0
    caddc
    @28
    @2
    cC
    cc0
    iffalse
    oveq12d
    00id
    syl6eq
    @2
    @0
    cc0
    iffalse
    eqtr4d
    pm2.61i
    mpteq2i
    syl6eq
    fveq2d
    3eqtr2d
    eqtr4d
end
