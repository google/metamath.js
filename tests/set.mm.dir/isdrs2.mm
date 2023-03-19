include "cdrs.mm"
include "wcel.mm"
include "cpreset.mm"
include "cv.mm"
include "wbr.mm"
include "wral.mm"
include "wrex.mm"
include "cpw.mm"
include "cfn.mm"
include "cin.mm"
include "wa.mm"
include "drsprs.mm"
include "wss.mm"
include "simpl.mm"
include "inss1.mm"
include "sseli.mm"
include "elpwid.mm"
include "adantl.mm"
include "inss2.mm"
include "drsdirfi.mm"
include "syl3anc.mm"
include "ralrimiva.mm"
include "jca.mm"
include "c0.mm"
include "wne.mm"
include "wi.mm"
include "0elpw.mm"
include "0fin.mm"
include "elin.mm"
include "mpbir2an.mm"
include "wceq.mm"
include "raleq.mm"
include "rexbidv.mm"
include "rspcv.mm"
include "ax-mp.mm"
include "rexn0.mm"
include "syl.mm"
include "cpr.mm"
include "prelpwi.mm"
include "prfi.mm"
include "a1i.mm"
include "elind.mm"
include "simplr.mm"
include "rspcva.mm"
include "syl2anc.mm"
include "vex.mm"
include "breq1.mm"
include "ralpr.mm"
include "rexbii.mm"
include "sylib.mm"
include "ralrimivva.mm"
include "isdrs.mm"
include "syl3anbrc.mm"
include "impbii.mm"

theorem isdrs2
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let cK: class K
  let c.le: class .<_
  let va: setvar a
  let vb: setvar b
  let vc: setvar c
  let cX: class X
  assume drsbn0.b: |- B = ( Base ` K )
  assume drsdirfi.l: |- .<_ = ( le ` K )

  disjoint K x
  disjoint K y
  disjoint K z
  disjoint x y
  disjoint x z
  disjoint y z
  disjoint B x
  disjoint B y
  disjoint B z
  disjoint .<_ x
  disjoint .<_ y
  disjoint .<_ z
  disjoint K a
  disjoint K b
  disjoint K c
  disjoint a b
  disjoint a c
  disjoint a x
  disjoint a y
  disjoint a z
  disjoint b c
  disjoint b x
  disjoint b y
  disjoint b z
  disjoint c x
  disjoint c y
  disjoint c z
  disjoint .<_ a
  disjoint .<_ b
  disjoint .<_ c
  disjoint B a
  disjoint B b
  disjoint B c
  disjoint X a
  disjoint X b
  disjoint X c
  disjoint X x
  disjoint X y
  disjoint X z
  assert |- ( K e. Dirset <-> ( K e. Preset /\ A. x e. ( ~P B i^i Fin ) E. y e. B A. z e. x z .<_ y ) )

  proof
    cK
    cdrs
    wcel
    #
    cK
    cpreset
    wcel
    #
    vz
    cv
    #
    vy
    cv
    #
    c.le
    wbr
    #
    vz
    vx
    cv
    #
    wral
    #
    vy
    cB
    wrex
    #
    vx
    cB
    cpw
    #
    cfn
    cin
    #
    wral
    #
    wa
    #
    @0
    @1
    @10
    cK
    drsprs
    @0
    @7
    vx
    @9
    @0
    @5
    @9
    wcel
    #
    wa
    @0
    @5
    cB
    wss
    #
    @5
    cfn
    wcel
    #
    @7
    @0
    @12
    simpl
    @12
    @13
    @0
    @12
    @5
    cB
    @9
    @8
    @5
    @8
    cfn
    inss1
    sseli
    elpwid
    adantl
    @12
    @14
    @0
    @9
    cfn
    @5
    @8
    cfn
    inss2
    sseli
    adantl
    vy
    vz
    cB
    cK
    c.le
    @5
    drsbn0.b
    drsdirfi.l
    drsdirfi
    syl3anc
    ralrimiva
    jca
    @11
    @1
    cB
    c0
    wne
    #
    va
    cv
    #
    @3
    c.le
    wbr
    #
    vb
    cv
    #
    @3
    c.le
    wbr
    #
    wa
    #
    vy
    cB
    wrex
    #
    vb
    cB
    wral
    va
    cB
    wral
    @0
    @1
    @10
    simpl
    @10
    @15
    @1
    @10
    @4
    vz
    c0
    wral
    #
    vy
    cB
    wrex
    #
    @15
    c0
    @9
    wcel
    #
    @10
    @23
    wi
    @24
    c0
    @8
    wcel
    c0
    cfn
    wcel
    cB
    0elpw
    0fin
    c0
    @8
    cfn
    elin
    mpbir2an
    @7
    @23
    vx
    c0
    @9
    @5
    c0
    wceq
    @6
    @22
    vy
    cB
    @4
    vz
    @5
    c0
    raleq
    rexbidv
    rspcv
    ax-mp
    @22
    vy
    cB
    rexn0
    syl
    adantl
    @11
    @21
    va
    vb
    cB
    cB
    @11
    @16
    cB
    wcel
    @18
    cB
    wcel
    wa
    #
    wa
    #
    @4
    vz
    @16
    @18
    cpr
    #
    wral
    #
    vy
    cB
    wrex
    #
    @21
    @26
    @27
    @9
    wcel
    #
    @10
    @29
    @25
    @30
    @11
    @25
    @8
    cfn
    @27
    @16
    @18
    cB
    prelpwi
    @27
    cfn
    wcel
    @25
    @16
    @18
    prfi
    a1i
    elind
    adantl
    @1
    @10
    @25
    simplr
    @7
    @29
    vx
    @27
    @9
    @5
    @27
    wceq
    @6
    @28
    vy
    cB
    @4
    vz
    @5
    @27
    raleq
    rexbidv
    rspcva
    syl2anc
    @28
    @20
    vy
    cB
    @4
    @17
    @19
    vz
    @16
    @18
    va
    vex
    vb
    vex
    @2
    @16
    @3
    c.le
    breq1
    @2
    @18
    @3
    c.le
    breq1
    ralpr
    rexbii
    sylib
    ralrimivva
    va
    vb
    vy
    cB
    cK
    c.le
    drsbn0.b
    drsdirfi.l
    isdrs
    syl3anbrc
    impbii
end
