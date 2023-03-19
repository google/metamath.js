include "cc0.mm"
include "cv.mm"
include "cre.mm"
include "cfv.mm"
include "cle.mm"
include "wbr.mm"
include "cc.mm"
include "crab.mm"
include "wcel.mm"
include "cneg.mm"
include "wss.mm"
include "ssrab2.mm"
include "a1i.mm"
include "cdif.mm"
include "wa.mm"
include "eldifi.mm"
include "adantl.mm"
include "recld.mm"
include "renegcld.mm"
include "clt.mm"
include "wn.mm"
include "wceq.mm"
include "fveq2.mm"
include "breq2d.mm"
include "notbid.mm"
include "notrab.mm"
include "elrab2.mm"
include "simprbi.mm"
include "cr.mm"
include "wb.mm"
include "0re.mm"
include "ltnle.mm"
include "sylancl.mm"
include "mpbird.mm"
include "lt0neg1d.mm"
include "mpbid.mm"
include "elrpd.mm"
include "cmin.mm"
include "co.mm"
include "cabs.mm"
include "adantr.mm"
include "elrabi.mm"
include "subcld.mm"
include "abscld.mm"
include "0red.mm"
include "elrab.mm"
include "lesub1dd.mm"
include "df-neg.mm"
include "resubd.mm"
include "3brtr4d.mm"
include "releabsd.mm"
include "letrd.mm"
include "sylanbrc.mm"
include "rlimcld2.mm"
include "syl.mm"

theorem rlimrege0
  let wph: wff ph
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cC: class C
  let vr: setvar r
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let cD: class D
  let cR: class R
  assume rlimcld2.1: |- ( ph -> sup ( A , RR* , < ) = +oo )
  assume rlimcld2.2: |- ( ph -> ( x e. A |-> B ) ~~>r C )
  assume rlimrege0.4: |- ( ( ph /\ x e. A ) -> B e. CC )
  assume rlimrege0.5: |- ( ( ph /\ x e. A ) -> 0 <_ ( Re ` B ) )

  disjoint A x
  disjoint C x
  disjoint ph x
  disjoint r x
  disjoint r y
  disjoint r z
  disjoint A r
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint r w
  disjoint B r
  disjoint w y
  disjoint w z
  disjoint B w
  disjoint B y
  disjoint B z
  disjoint C r
  disjoint w x
  disjoint C w
  disjoint C y
  disjoint C z
  disjoint ph r
  disjoint ph y
  disjoint ph z
  disjoint D r
  disjoint D x
  disjoint D y
  disjoint D z
  disjoint R r
  disjoint R x
  disjoint R z
  assert |- ( ph -> 0 <_ ( Re ` C ) )

  proof
    wph
    cC
    cc0
    vw
    cv
    #
    cre
    cfv
    #
    cle
    wbr
    #
    vw
    cc
    crab
    #
    wcel
    #
    cc0
    cC
    cre
    cfv
    #
    cle
    wbr
    #
    wph
    vx
    vy
    vz
    cA
    cB
    cC
    @3
    vy
    cv
    #
    cre
    cfv
    #
    cneg
    #
    rlimcld2.1
    rlimcld2.2
    @3
    cc
    wss
    wph
    @2
    vw
    cc
    ssrab2
    a1i
    wph
    @7
    cc
    @3
    cdif
    #
    wcel
    #
    wa
    #
    @9
    @12
    @8
    @12
    @7
    @11
    @7
    cc
    wcel
    #
    wph
    @7
    cc
    @3
    eldifi
    adantl
    #
    recld
    #
    renegcld
    #
    @12
    @8
    cc0
    clt
    wbr
    #
    cc0
    @9
    clt
    wbr
    @12
    @17
    cc0
    @8
    cle
    wbr
    #
    wn
    #
    @11
    @19
    wph
    @11
    @13
    @19
    @2
    wn
    @19
    vw
    @7
    cc
    @10
    @0
    @7
    wceq
    #
    @2
    @18
    @20
    @1
    @8
    cc0
    cle
    @0
    @7
    cre
    fveq2
    breq2d
    notbid
    @2
    vw
    cc
    notrab
    elrab2
    simprbi
    adantl
    @12
    @8
    cr
    wcel
    cc0
    cr
    wcel
    @17
    @19
    wb
    @15
    0re
    @8
    cc0
    ltnle
    sylancl
    mpbird
    @12
    @8
    @15
    lt0neg1d
    mpbid
    elrpd
    @12
    vz
    cv
    #
    @3
    wcel
    #
    wa
    #
    @9
    @21
    @7
    cmin
    co
    #
    cre
    cfv
    #
    @24
    cabs
    cfv
    @12
    @9
    cr
    wcel
    @22
    @16
    adantr
    @23
    @24
    @23
    @21
    @7
    @22
    @21
    cc
    wcel
    #
    @12
    @2
    vw
    @21
    cc
    elrabi
    adantl
    #
    @12
    @13
    @22
    @14
    adantr
    #
    subcld
    #
    recld
    @23
    @24
    @29
    abscld
    @23
    cc0
    @8
    cmin
    co
    #
    @21
    cre
    cfv
    #
    @8
    cmin
    co
    @9
    @25
    cle
    @23
    cc0
    @31
    @8
    @23
    0red
    @23
    @21
    @27
    recld
    @23
    @7
    @28
    recld
    @22
    cc0
    @31
    cle
    wbr
    #
    @12
    @22
    @26
    @32
    @2
    @32
    vw
    @21
    cc
    @0
    @21
    wceq
    @1
    @31
    cc0
    cle
    @0
    @21
    cre
    fveq2
    breq2d
    elrab
    simprbi
    adantl
    lesub1dd
    @9
    @30
    wceq
    @23
    @8
    df-neg
    a1i
    @23
    @21
    @7
    @27
    @28
    resubd
    3brtr4d
    @23
    @24
    @29
    releabsd
    letrd
    wph
    vx
    cv
    cA
    wcel
    wa
    cB
    cc
    wcel
    cc0
    cB
    cre
    cfv
    #
    cle
    wbr
    #
    cB
    @3
    wcel
    rlimrege0.4
    rlimrege0.5
    @2
    @34
    vw
    cB
    cc
    @0
    cB
    wceq
    @1
    @33
    cc0
    cle
    @0
    cB
    cre
    fveq2
    breq2d
    elrab
    sylanbrc
    rlimcld2
    @4
    cC
    cc
    wcel
    @6
    @2
    @6
    vw
    cC
    cc
    @0
    cC
    wceq
    @1
    @5
    cc0
    cle
    @0
    cC
    cre
    fveq2
    breq2d
    elrab
    simprbi
    syl
end
