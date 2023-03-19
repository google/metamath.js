include "cr.mm"
include "wcel.mm"
include "cfl.mm"
include "cfv.mm"
include "cv.mm"
include "cle.mm"
include "wbr.mm"
include "cz.mm"
include "crab.mm"
include "clt.mm"
include "csup.mm"
include "wceq.mm"
include "wss.mm"
include "c0.mm"
include "wne.mm"
include "wral.mm"
include "wrex.mm"
include "ssrab2.mm"
include "zssre.mm"
include "sstri.mm"
include "a1i.mm"
include "flcl.mm"
include "flle.mm"
include "breq1.mm"
include "elrab.mm"
include "sylanbrc.mm"
include "ne0i.mm"
include "syl.mm"
include "reflcl.mm"
include "wa.mm"
include "flge.mm"
include "biimpd.mm"
include "expimpd.mm"
include "syl5bi.mm"
include "ralrimiv.mm"
include "breq2.mm"
include "ralbidv.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "suprub.mm"
include "syl31anc.mm"
include "wb.mm"
include "suprleub.mm"
include "mpbird.mm"
include "suprcl.mm"
include "syl3anc.mm"
include "letri3d.mm"
include "mpbir2and.mm"

theorem flval3
  let vx: setvar x
  let cA: class A
  let vy: setvar y
  let vz: setvar z
  let cB: class B

  disjoint A x
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint A y
  disjoint A z
  disjoint B x
  disjoint B y
  assert |- ( A e. RR -> ( |_ ` A ) = sup ( { x e. ZZ | x <_ A } , RR , < ) )

  proof
    cA
    cr
    wcel
    #
    cA
    cfl
    cfv
    #
    vx
    cv
    #
    cA
    cle
    wbr
    #
    vx
    cz
    crab
    #
    cr
    clt
    csup
    #
    wceq
    @1
    @5
    cle
    wbr
    #
    @5
    @1
    cle
    wbr
    #
    @0
    @4
    cr
    wss
    #
    @4
    c0
    wne
    #
    vz
    cv
    #
    vy
    cv
    #
    cle
    wbr
    #
    vz
    @4
    wral
    #
    vy
    cr
    wrex
    #
    @1
    @4
    wcel
    #
    @6
    @8
    @0
    @4
    cz
    cr
    @3
    vx
    cz
    ssrab2
    zssre
    sstri
    a1i
    #
    @0
    @15
    @9
    @0
    @1
    cz
    wcel
    @1
    cA
    cle
    wbr
    #
    @15
    cA
    flcl
    cA
    flle
    @3
    @17
    vx
    @1
    cz
    @2
    @1
    cA
    cle
    breq1
    elrab
    sylanbrc
    #
    @4
    @1
    ne0i
    syl
    #
    @0
    @1
    cr
    wcel
    #
    @10
    @1
    cle
    wbr
    #
    vz
    @4
    wral
    #
    @14
    cA
    reflcl
    #
    @0
    @21
    vz
    @4
    @10
    @4
    wcel
    @10
    cz
    wcel
    #
    @10
    cA
    cle
    wbr
    #
    wa
    @0
    @21
    @3
    @25
    vx
    @10
    cz
    @2
    @10
    cA
    cle
    breq1
    elrab
    @0
    @24
    @25
    @21
    @0
    @24
    wa
    @25
    @21
    cA
    @10
    flge
    biimpd
    expimpd
    syl5bi
    ralrimiv
    #
    @13
    @22
    vy
    @1
    cr
    @11
    @1
    wceq
    @12
    @21
    vz
    @4
    @11
    @1
    @10
    cle
    breq2
    ralbidv
    rspcev
    syl2anc
    #
    @18
    vy
    vz
    @4
    @1
    suprub
    syl31anc
    @0
    @7
    @22
    @26
    @0
    @8
    @9
    @14
    @20
    @7
    @22
    wb
    @16
    @19
    @27
    @23
    vy
    vz
    vz
    @4
    @1
    suprleub
    syl31anc
    mpbird
    @0
    @1
    @5
    @23
    @0
    @8
    @9
    @14
    @5
    cr
    wcel
    @16
    @19
    @27
    vy
    vz
    @4
    suprcl
    syl3anc
    letri3d
    mpbir2and
end
