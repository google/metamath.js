include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "csn.mm"
include "crsp.mm"
include "cfv.mm"
include "wceq.mm"
include "cbs.mm"
include "wrex.mm"
include "wbr.mm"
include "wral.mm"
include "wb.mm"
include "eqid.mm"
include "islpidl.mm"
include "adantr.mm"
include "lidldvgen.mm"
include "3expa.mm"
include "rexbidva.mm"
include "simpr.mm"
include "wss.mm"
include "lidlss.mm"
include "adantl.mm"
include "sseld.mm"
include "adantrd.mm"
include "ancrd.mm"
include "impbid2.mm"
include "rexbidv2.mm"
include "3bitrd.mm"

theorem lpigen
  let vx: setvar x
  let vy: setvar y
  let c.pa: class .||
  let cP: class P
  let cR: class R
  let cU: class U
  let cI: class I
  assume lpigen.u: |- U = ( LIdeal ` R )
  assume lpigen.p: |- P = ( LPIdeal ` R )
  assume lpigen.d: |- .|| = ( ||r ` R )

  disjoint R x
  disjoint R y
  disjoint x y
  disjoint I x
  disjoint I y
  disjoint U x
  disjoint U y
  disjoint P x
  disjoint P y
  disjoint .|| x
  disjoint .|| y
  assert |- ( ( R e. Ring /\ I e. U ) -> ( I e. P <-> E. x e. I A. y e. I x .|| y ) )

  proof
    cR
    crg
    wcel
    #
    cI
    cU
    wcel
    #
    wa
    #
    cI
    cP
    wcel
    #
    cI
    vx
    cv
    #
    csn
    cR
    crsp
    cfv
    #
    cfv
    wceq
    #
    vx
    cR
    cbs
    cfv
    #
    wrex
    #
    @4
    cI
    wcel
    #
    @4
    vy
    cv
    c.pa
    wbr
    vy
    cI
    wral
    #
    wa
    #
    vx
    @7
    wrex
    @10
    vx
    cI
    wrex
    @0
    @3
    @8
    wb
    @1
    @7
    cP
    cR
    vx
    cI
    @5
    lpigen.p
    @5
    eqid
    #
    @7
    eqid
    #
    islpidl
    adantr
    @2
    @6
    @11
    vx
    @7
    @0
    @1
    @4
    @7
    wcel
    #
    @6
    @11
    wb
    vy
    @7
    c.pa
    cR
    cU
    @4
    cI
    @5
    @13
    lpigen.u
    @12
    lpigen.d
    lidldvgen
    3expa
    rexbidva
    @2
    @11
    @10
    vx
    @7
    cI
    @2
    @14
    @11
    wa
    @11
    @14
    @11
    simpr
    @2
    @11
    @14
    @2
    @9
    @14
    @10
    @2
    cI
    @7
    @4
    @1
    cI
    @7
    wss
    @0
    @7
    cI
    cU
    cR
    @13
    lpigen.u
    lidlss
    adantl
    sseld
    adantrd
    ancrd
    impbid2
    rexbidv2
    3bitrd
end
