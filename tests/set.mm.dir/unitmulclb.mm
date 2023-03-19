include "ccrg.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "wa.mm"
include "cdsr.mm"
include "cfv.mm"
include "wbr.mm"
include "wi.mm"
include "simp1.mm"
include "simp2.mm"
include "simp3.mm"
include "eqid.mm"
include "dvdsrmul.mm"
include "syl2anc.mm"
include "crngcom.mm"
include "breqtrrd.mm"
include "dvdsunit.mm"
include "3expia.mm"
include "jcad.mm"
include "crg.mm"
include "crngring.mm"
include "3ad2ant1.mm"
include "unitmulcl.mm"
include "3expib.mm"
include "syl.mm"
include "impbid.mm"

theorem unitmulclb
  let cB: class B
  let cR: class R
  let c.x: class .x.
  let cU: class U
  let cX: class X
  let cY: class Y
  assume unitmulcl.1: |- U = ( Unit ` R )
  assume unitmulcl.2: |- .x. = ( .r ` R )
  assume unitmulclb.1: |- B = ( Base ` R )


  assert |- ( ( R e. CRing /\ X e. B /\ Y e. B ) -> ( ( X .x. Y ) e. U <-> ( X e. U /\ Y e. U ) ) )

  proof
    cR
    ccrg
    wcel
    #
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    w3a
    #
    cX
    cY
    c.x
    co
    #
    cU
    wcel
    #
    cX
    cU
    wcel
    #
    cY
    cU
    wcel
    #
    wa
    #
    @3
    @5
    @6
    @7
    @3
    @0
    cX
    @4
    cR
    cdsr
    cfv
    #
    wbr
    #
    @5
    @6
    wi
    @0
    @1
    @2
    simp1
    #
    @3
    cX
    cY
    cX
    c.x
    co
    #
    @4
    @9
    @3
    @1
    @2
    cX
    @12
    @9
    wbr
    @0
    @1
    @2
    simp2
    #
    @0
    @1
    @2
    simp3
    #
    cB
    @9
    cR
    c.x
    cX
    cY
    unitmulclb.1
    @9
    eqid
    #
    unitmulcl.2
    dvdsrmul
    syl2anc
    cB
    cR
    c.x
    cX
    cY
    unitmulclb.1
    unitmulcl.2
    crngcom
    breqtrrd
    @0
    @10
    @5
    @6
    @9
    cR
    cU
    @4
    cX
    unitmulcl.1
    @15
    dvdsunit
    3expia
    syl2anc
    @3
    @0
    cY
    @4
    @9
    wbr
    #
    @5
    @7
    wi
    @11
    @3
    @2
    @1
    @16
    @14
    @13
    cB
    @9
    cR
    c.x
    cY
    cX
    unitmulclb.1
    @15
    unitmulcl.2
    dvdsrmul
    syl2anc
    @0
    @16
    @5
    @7
    @9
    cR
    cU
    @4
    cY
    unitmulcl.1
    @15
    dvdsunit
    3expia
    syl2anc
    jcad
    @3
    cR
    crg
    wcel
    #
    @8
    @5
    wi
    @0
    @1
    @17
    @2
    cR
    crngring
    3ad2ant1
    @17
    @6
    @7
    @5
    cR
    c.x
    cU
    cX
    cY
    unitmulcl.1
    unitmulcl.2
    unitmulcl
    3expib
    syl
    impbid
end
