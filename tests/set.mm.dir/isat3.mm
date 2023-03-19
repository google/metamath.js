include "cal.mm"
include "wcel.mm"
include "wne.mm"
include "cv.mm"
include "wbr.mm"
include "wceq.mm"
include "wo.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "w3a.mm"
include "ccvr.mm"
include "cfv.mm"
include "eqid.mm"
include "isat.mm"
include "cplt.mm"
include "wb.mm"
include "simpl.mm"
include "atl0cl.mm"
include "adantr.mm"
include "simpr.mm"
include "cvrval2.mm"
include "syl3anc.mm"
include "atlltn0.mm"
include "adantlr.mm"
include "imbi1d.mm"
include "imbi2d.mm"
include "impexp.mm"
include "bi2.04.mm"
include "bitri.mm"
include "orcom.mm"
include "neor.mm"
include "imbi2i.mm"
include "3bitr4g.mm"
include "ralbidva.mm"
include "anbi12d.mm"
include "bitr2d.mm"
include "pm5.32da.mm"
include "bitr4d.mm"
include "3anass.mm"
include "syl6bbr.mm"

theorem isat3
  let vx: setvar x
  let cA: class A
  let cB: class B
  let cP: class P
  let cK: class K
  let c.le: class .<_
  let c.0: class .0.
  assume isat3.b: |- B = ( Base ` K )
  assume isat3.l: |- .<_ = ( le ` K )
  assume isat3.z: |- .0. = ( 0. ` K )
  assume isat3.a: |- A = ( Atoms ` K )

  disjoint B x
  disjoint K x
  disjoint P x
  disjoint .0. x
  assert |- ( K e. AtLat -> ( P e. A <-> ( P e. B /\ P =/= .0. /\ A. x e. B ( x .<_ P -> ( x = P \/ x = .0. ) ) ) ) )

  proof
    cK
    cal
    wcel
    #
    cP
    cA
    wcel
    #
    cP
    cB
    wcel
    #
    cP
    c.0
    wne
    #
    vx
    cv
    #
    cP
    c.le
    wbr
    #
    @4
    cP
    wceq
    #
    @4
    c.0
    wceq
    #
    wo
    #
    wi
    #
    vx
    cB
    wral
    #
    wa
    #
    wa
    #
    @2
    @3
    @10
    w3a
    @0
    @1
    @2
    c.0
    cP
    cK
    ccvr
    cfv
    #
    wbr
    #
    wa
    @12
    cA
    cB
    @13
    cal
    cP
    cK
    c.0
    isat3.b
    isat3.z
    @13
    eqid
    #
    isat3.a
    isat
    @0
    @2
    @11
    @14
    @0
    @2
    wa
    #
    @14
    c.0
    cP
    cK
    cplt
    cfv
    #
    wbr
    #
    c.0
    @4
    @17
    wbr
    #
    @5
    wa
    @6
    wi
    #
    vx
    cB
    wral
    #
    wa
    #
    @11
    @16
    @0
    c.0
    cB
    wcel
    #
    @2
    @14
    @22
    wb
    @0
    @2
    simpl
    @0
    @23
    @2
    cB
    cK
    c.0
    isat3.b
    isat3.z
    atl0cl
    adantr
    @0
    @2
    simpr
    vx
    cal
    cB
    @13
    @17
    cK
    c.le
    c.0
    cP
    isat3.b
    isat3.l
    @17
    eqid
    #
    @15
    cvrval2
    syl3anc
    @16
    @18
    @3
    @21
    @10
    cB
    @17
    cK
    cP
    c.0
    isat3.b
    @24
    isat3.z
    atlltn0
    @16
    @20
    @9
    vx
    cB
    @16
    @4
    cB
    wcel
    #
    wa
    #
    @5
    @19
    @6
    wi
    #
    wi
    #
    @5
    @4
    c.0
    wne
    #
    @6
    wi
    #
    wi
    @20
    @9
    @26
    @27
    @30
    @5
    @26
    @19
    @29
    @6
    @0
    @25
    @19
    @29
    wb
    @2
    cB
    @17
    cK
    @4
    c.0
    isat3.b
    @24
    isat3.z
    atlltn0
    adantlr
    imbi1d
    imbi2d
    @20
    @19
    @5
    @6
    wi
    wi
    @28
    @19
    @5
    @6
    impexp
    @19
    @5
    @6
    bi2.04
    bitri
    @8
    @30
    @5
    @8
    @7
    @6
    wo
    @30
    @6
    @7
    orcom
    @6
    @4
    c.0
    neor
    bitri
    imbi2i
    3bitr4g
    ralbidva
    anbi12d
    bitr2d
    pm5.32da
    bitr4d
    @2
    @3
    @10
    3anass
    syl6bbr
end
