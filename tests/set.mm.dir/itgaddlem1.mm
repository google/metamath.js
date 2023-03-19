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
include "ibladd.mm"
include "addge0d.mm"
include "itgposval.mm"
include "cof.mm"
include "oveq12d.mm"
include "cpnf.mm"
include "cico.mm"
include "cvol.mm"
include "cdm.mm"
include "wss.mm"
include "cmbf.mm"
include "cibl.mm"
include "iblpos.mm"
include "mpbid.mm"
include "simpld.mm"
include "mbfdm2.mm"
include "mblss.mm"
include "syl.mm"
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
include "eldifn.mm"
include "adantl.mm"
include "iffalsed.mm"
include "iftrue.mm"
include "mpteq2ia.mm"
include "syl5eqel.mm"
include "mbfss.mm"
include "eqid.mm"
include "fmptd.mm"
include "simprd.mm"
include "itg2add.mm"
include "cvv.mm"
include "reex.mm"
include "eqidd.mm"
include "offval2.mm"
include "wceq.mm"
include "eqtr4d.mm"
include "iffalse.mm"
include "00id.mm"
include "syl6eq.mm"
include "pm2.61i.mm"
include "mpteq2i.mm"
include "fveq2d.mm"
include "3eqtr2d.mm"

theorem itgaddlem1
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let cV: class V
  assume itgadd.1: |- ( ( ph /\ x e. A ) -> B e. V )
  assume itgadd.2: |- ( ph -> ( x e. A |-> B ) e. L^1 )
  assume itgadd.3: |- ( ( ph /\ x e. A ) -> C e. V )
  assume itgadd.4: |- ( ph -> ( x e. A |-> C ) e. L^1 )
  assume itgadd.5: |- ( ( ph /\ x e. A ) -> B e. RR )
  assume itgadd.6: |- ( ( ph /\ x e. A ) -> C e. RR )
  assume itgadd.7: |- ( ( ph /\ x e. A ) -> 0 <_ B )
  assume itgadd.8: |- ( ( ph /\ x e. A ) -> 0 <_ C )

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
    itgadd.5
    itgadd.6
    readdcld
    wph
    vx
    cA
    cB
    cC
    cV
    itgadd.1
    itgadd.2
    itgadd.3
    itgadd.4
    ibladd
    @9
    cB
    cC
    itgadd.5
    itgadd.6
    itgadd.7
    itgadd.8
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
    itgadd.5
    itgadd.2
    itgadd.7
    itgposval
    wph
    vx
    cA
    cC
    itgadd.6
    itgadd.4
    itgadd.8
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
    cr
    wph
    vx
    cA
    cB
    cmpt
    #
    cmbf
    wcel
    #
    @12
    cr
    wcel
    #
    wph
    @19
    cibl
    wcel
    @20
    @21
    wa
    itgadd.2
    wph
    vx
    cA
    cB
    itgadd.5
    itgadd.7
    iblpos
    mpbid
    #
    simpld
    #
    itgadd.5
    mbfdm2
    cA
    mblss
    syl
    #
    cr
    @18
    wcel
    wph
    rembl
    a1i
    #
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
    itgadd.5
    itgadd.7
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
    #
    @2
    cB
    cc0
    @30
    @27
    wph
    @1
    cr
    cA
    eldifn
    adantl
    #
    iffalsed
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
    @23
    syl5eqel
    mbfss
    wph
    vx
    cr
    @10
    @17
    @11
    wph
    @26
    @1
    cr
    wcel
    #
    @29
    adantr
    #
    @11
    eqid
    fmptd
    wph
    @20
    @21
    @22
    simprd
    wph
    vx
    cA
    cr
    @13
    @17
    @24
    @25
    wph
    @13
    @17
    wcel
    #
    @2
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
    itgadd.6
    itgadd.8
    cC
    elrege0
    sylanbrc
    @28
    ifclda
    #
    adantr
    @31
    @2
    cC
    cc0
    @32
    iffalsed
    wph
    vx
    cA
    @13
    cmpt
    vx
    cA
    cC
    cmpt
    #
    cmbf
    vx
    cA
    @13
    cC
    @2
    cC
    cc0
    iftrue
    #
    mpteq2ia
    wph
    @38
    cmbf
    wcel
    #
    @15
    cr
    wcel
    #
    wph
    @38
    cibl
    wcel
    @40
    @41
    wa
    itgadd.4
    wph
    vx
    cA
    cC
    itgadd.6
    itgadd.8
    iblpos
    mpbid
    #
    simpld
    syl5eqel
    mbfss
    wph
    vx
    cr
    @13
    @17
    @14
    wph
    @36
    @34
    @37
    adantr
    #
    @14
    eqid
    fmptd
    wph
    @40
    @41
    @42
    simprd
    itg2add
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
    @35
    @43
    wph
    @11
    eqidd
    wph
    @14
    eqidd
    offval2
    vx
    cr
    @44
    @3
    @2
    @44
    @3
    wceq
    @2
    @44
    @0
    @3
    @2
    @10
    cB
    @13
    cC
    caddc
    @33
    @39
    oveq12d
    @2
    @0
    cc0
    iftrue
    eqtr4d
    @27
    @44
    cc0
    @3
    @27
    @44
    cc0
    cc0
    caddc
    co
    cc0
    @27
    @10
    cc0
    @13
    cc0
    caddc
    @2
    cB
    cc0
    iffalse
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
