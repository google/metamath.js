include "wcel.mm"
include "wss.mm"
include "wa.mm"
include "cmgm.mm"
include "cv.mm"
include "co.mm"
include "wral.mm"
include "cplusg.mm"
include "cfv.mm"
include "cbs.mm"
include "simplr.mm"
include "wi.mm"
include "wceq.mm"
include "ressbas2.mm"
include "syl.mm"
include "eleq2d.mm"
include "biimpcd.mm"
include "adantr.mm"
include "impcom.mm"
include "adantl.mm"
include "eqid.mm"
include "mgmcl.mm"
include "syl3anc.mm"
include "cvv.mm"
include "fvex.mm"
include "eqeltri.mm"
include "ssex.mm"
include "ressplusg.mm"
include "oveqdr.mm"
include "3eltr4d.mm"
include "ralrimivva.mm"
include "oveqd.mm"
include "eleq12d.mm"
include "raleqbidv.mm"
include "biimpa.mm"
include "wb.mm"
include "ismgm.mm"
include "ad2antrr.mm"
include "mpbird.mm"
include "impbida.mm"

theorem issstrmgm
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let c.pl: class .+
  let cS: class S
  let cG: class G
  let cH: class H
  let cV: class V
  assume issstrmgm.b: |- B = ( Base ` G )
  assume issstrmgm.p: |- .+ = ( +g ` G )
  assume issstrmgm.h: |- H = ( G |`s S )

  disjoint B x
  disjoint B y
  disjoint x y
  disjoint H x
  disjoint H y
  disjoint S x
  disjoint S y
  disjoint V x
  disjoint V y
  assert |- ( ( H e. V /\ S C_ B ) -> ( H e. Mgm <-> A. x e. S A. y e. S ( x .+ y ) e. S ) )

  proof
    cH
    cV
    wcel
    #
    cS
    cB
    wss
    #
    wa
    #
    cH
    cmgm
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    c.pl
    co
    #
    cS
    wcel
    #
    vy
    cS
    wral
    #
    vx
    cS
    wral
    #
    @2
    @3
    wa
    #
    @7
    vx
    vy
    cS
    cS
    @10
    @4
    cS
    wcel
    #
    @5
    cS
    wcel
    #
    wa
    #
    wa
    #
    @4
    @5
    cH
    cplusg
    cfv
    #
    co
    #
    cH
    cbs
    cfv
    #
    @6
    cS
    @14
    @3
    @4
    @17
    wcel
    #
    @5
    @17
    wcel
    #
    @16
    @17
    wcel
    #
    @2
    @3
    @13
    simplr
    @13
    @10
    @18
    @11
    @10
    @18
    wi
    @12
    @10
    @11
    @18
    @10
    cS
    @17
    @4
    @10
    @1
    cS
    @17
    wceq
    #
    @0
    @1
    @3
    simplr
    cS
    cB
    cH
    cG
    issstrmgm.h
    issstrmgm.b
    ressbas2
    #
    syl
    #
    eleq2d
    biimpcd
    adantr
    impcom
    @13
    @10
    @19
    @12
    @10
    @19
    wi
    @11
    @10
    @12
    @19
    @10
    cS
    @17
    @5
    @23
    eleq2d
    biimpcd
    adantl
    impcom
    @17
    cH
    @4
    @5
    @15
    @17
    eqid
    #
    @15
    eqid
    #
    mgmcl
    syl3anc
    @10
    @13
    vx
    vy
    c.pl
    @15
    @2
    c.pl
    @15
    wceq
    #
    @3
    @2
    cS
    cvv
    wcel
    #
    @26
    @1
    @27
    @0
    cS
    cB
    cB
    cG
    cbs
    cfv
    cvv
    issstrmgm.b
    cG
    cbs
    fvex
    eqeltri
    ssex
    adantl
    cS
    c.pl
    cG
    cH
    cvv
    issstrmgm.h
    issstrmgm.p
    ressplusg
    syl
    #
    adantr
    oveqdr
    @10
    @21
    @13
    @23
    adantr
    3eltr4d
    ralrimivva
    @2
    @9
    wa
    @3
    @20
    vy
    @17
    wral
    #
    vx
    @17
    wral
    #
    @2
    @9
    @30
    @2
    @8
    @29
    vx
    cS
    @17
    @1
    @21
    @0
    @22
    adantl
    #
    @2
    @7
    @20
    vy
    cS
    @17
    @31
    @2
    @6
    @16
    cS
    @17
    @2
    c.pl
    @15
    @4
    @5
    @28
    oveqd
    @31
    eleq12d
    raleqbidv
    raleqbidv
    biimpa
    @0
    @3
    @30
    wb
    @1
    @9
    vx
    vy
    @17
    cH
    cV
    @15
    @24
    @25
    ismgm
    ad2antrr
    mpbird
    impbida
end
