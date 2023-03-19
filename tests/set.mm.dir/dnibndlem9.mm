include "cfv.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "cle.mm"
include "wbr.mm"
include "c1.mm"
include "c2.mm"
include "cdiv.mm"
include "caddc.mm"
include "cfl.mm"
include "dnicld1.mm"
include "recnd.mm"
include "subcld.mm"
include "abscld.mm"
include "cr.mm"
include "wcel.mm"
include "wa.mm"
include "halfre.mm"
include "a1i.mm"
include "jca.mm"
include "resubcl.mm"
include "syl.mm"
include "readdcld.mm"
include "reflcl.mm"
include "addcld.mm"
include "dnibndlem6.mm"
include "dnibndlem7.mm"
include "dnibndlem8.mm"
include "le2addd.mm"
include "cc0.mm"
include "dnibndlem4.mm"
include "0red.mm"
include "clt.mm"
include "dnibndlem5.mm"
include "ltled.mm"
include "addge0d.mm"
include "absidd.mm"
include "eqcomd.mm"
include "breqtrd.mm"
include "letrd.mm"
include "dnibndlem3.mm"
include "dnibndlem1.mm"
include "mpbird.mm"

theorem dnibndlem9
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cT: class T
  assume dnibndlem9.1: |- T = ( x e. RR |-> ( abs ` ( ( |_ ` ( x + ( 1 / 2 ) ) ) - x ) ) )
  assume dnibndlem9.2: |- ( ph -> A e. RR )
  assume dnibndlem9.3: |- ( ph -> B e. RR )
  assume dnibndlem9.4: |- ( ph -> ( |_ ` ( B + ( 1 / 2 ) ) ) = ( ( |_ ` ( A + ( 1 / 2 ) ) ) + 1 ) )

  disjoint A x
  disjoint B x
  assert |- ( ph -> ( abs ` ( ( T ` B ) - ( T ` A ) ) ) <_ ( abs ` ( B - A ) ) )

  proof
    wph
    cB
    cT
    cfv
    cA
    cT
    cfv
    cmin
    co
    cabs
    cfv
    cB
    cA
    cmin
    co
    cabs
    cfv
    #
    cle
    wbr
    cB
    c1
    c2
    cdiv
    co
    #
    caddc
    co
    #
    cfl
    cfv
    #
    cB
    cmin
    co
    cabs
    cfv
    #
    cA
    @1
    caddc
    co
    #
    cfl
    cfv
    #
    cA
    cmin
    co
    cabs
    cfv
    #
    cmin
    co
    #
    cabs
    cfv
    #
    @0
    cle
    wbr
    wph
    @9
    cB
    @3
    @1
    cmin
    co
    #
    cmin
    co
    #
    @6
    @1
    caddc
    co
    #
    cA
    cmin
    co
    #
    caddc
    co
    #
    cabs
    cfv
    #
    @0
    cle
    wph
    @9
    @1
    @4
    cmin
    co
    #
    @1
    @7
    cmin
    co
    #
    caddc
    co
    #
    @15
    wph
    @8
    wph
    @4
    @7
    wph
    @4
    wph
    cB
    dnibndlem9.3
    dnicld1
    #
    recnd
    wph
    @7
    wph
    cA
    dnibndlem9.2
    dnicld1
    #
    recnd
    subcld
    abscld
    wph
    @16
    @17
    wph
    @1
    cr
    wcel
    #
    @4
    cr
    wcel
    #
    wa
    @16
    cr
    wcel
    wph
    @21
    @22
    @21
    wph
    halfre
    a1i
    #
    @19
    jca
    @1
    @4
    resubcl
    syl
    #
    wph
    @21
    @7
    cr
    wcel
    #
    wa
    @17
    cr
    wcel
    wph
    @21
    @25
    @23
    @20
    jca
    @1
    @7
    resubcl
    syl
    #
    readdcld
    wph
    @14
    wph
    @11
    @13
    wph
    cB
    @10
    wph
    cB
    dnibndlem9.3
    recnd
    wph
    @3
    @1
    wph
    @3
    wph
    @2
    cr
    wcel
    @3
    cr
    wcel
    #
    wph
    cB
    @1
    dnibndlem9.3
    @23
    readdcld
    @2
    reflcl
    syl
    #
    recnd
    wph
    @1
    @23
    recnd
    #
    subcld
    subcld
    wph
    @12
    cA
    wph
    @6
    @1
    wph
    @6
    wph
    @5
    cr
    wcel
    @6
    cr
    wcel
    wph
    cA
    @1
    dnibndlem9.2
    @23
    readdcld
    @5
    reflcl
    syl
    #
    recnd
    @29
    addcld
    wph
    cA
    dnibndlem9.2
    recnd
    subcld
    addcld
    abscld
    wph
    cA
    cB
    dnibndlem9.2
    dnibndlem9.3
    dnibndlem6
    wph
    @18
    @14
    @15
    cle
    wph
    @16
    @17
    @11
    @13
    @24
    @26
    wph
    cB
    cr
    wcel
    #
    @10
    cr
    wcel
    #
    wa
    @11
    cr
    wcel
    wph
    @31
    @32
    dnibndlem9.3
    wph
    @27
    @21
    wa
    @32
    wph
    @27
    @21
    @28
    @23
    jca
    @3
    @1
    resubcl
    syl
    jca
    cB
    @10
    resubcl
    syl
    #
    wph
    @12
    cr
    wcel
    #
    cA
    cr
    wcel
    #
    wa
    @13
    cr
    wcel
    wph
    @34
    @35
    wph
    @6
    @1
    @30
    @23
    readdcld
    dnibndlem9.2
    jca
    @12
    cA
    resubcl
    syl
    #
    wph
    cB
    dnibndlem9.3
    dnibndlem7
    wph
    cA
    dnibndlem9.2
    dnibndlem8
    le2addd
    wph
    @15
    @14
    wph
    @14
    wph
    @11
    @13
    @33
    @36
    readdcld
    wph
    @11
    @13
    @33
    @36
    wph
    @31
    cc0
    @11
    cle
    wbr
    dnibndlem9.3
    cB
    dnibndlem4
    syl
    wph
    cc0
    @13
    wph
    0red
    @36
    wph
    @35
    cc0
    @13
    clt
    wbr
    dnibndlem9.2
    cA
    dnibndlem5
    syl
    ltled
    addge0d
    absidd
    eqcomd
    breqtrd
    letrd
    wph
    @0
    @15
    wph
    vx
    cA
    cB
    cT
    dnibndlem9.1
    dnibndlem9.2
    dnibndlem9.3
    dnibndlem9.4
    dnibndlem3
    eqcomd
    breqtrd
    wph
    vx
    cA
    cB
    @0
    cT
    dnibndlem9.1
    dnibndlem9.2
    dnibndlem9.3
    dnibndlem1
    mpbird
end
