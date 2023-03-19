include "crg.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "wbr.mm"
include "csn.mm"
include "cfv.mm"
include "cmulr.mm"
include "co.mm"
include "wceq.mm"
include "wrex.mm"
include "wb.mm"
include "eqcom.mm"
include "a1i.mm"
include "rexbidv.mm"
include "crglmod.mm"
include "clmod.mm"
include "rlmlmod.mm"
include "cid.mm"
include "rlmsca2.mm"
include "cbs.mm"
include "cnx.mm"
include "baseid.mm"
include "strfvi.mm"
include "rlmbas.mm"
include "eqtri.mm"
include "rlmvsca.mm"
include "crsp.mm"
include "clspn.mm"
include "rspval.mm"
include "lspsnel.mm"
include "sylan.mm"
include "eqid.mm"
include "dvdsr2.mm"
include "adantl.mm"
include "3bitr4d.mm"
include "abbi2dv.mm"

theorem rspsn
  let vx: setvar x
  let cB: class B
  let c.pa: class .||
  let cR: class R
  let cG: class G
  let cK: class K
  let va: setvar a
  assume rspsn.b: |- B = ( Base ` R )
  assume rspsn.k: |- K = ( RSpan ` R )
  assume rspsn.d: |- .|| = ( ||r ` R )

  disjoint R x
  disjoint G x
  disjoint B x
  disjoint K x
  disjoint .|| x
  disjoint a x
  disjoint R a
  disjoint G a
  disjoint B a
  disjoint K a
  disjoint .|| a
  assert |- ( ( R e. Ring /\ G e. B ) -> ( K ` { G } ) = { x | G .|| x } )

  proof
    cR
    crg
    wcel
    #
    cG
    cB
    wcel
    #
    wa
    #
    cG
    vx
    cv
    #
    c.pa
    wbr
    #
    vx
    cG
    csn
    cK
    cfv
    #
    @2
    @3
    va
    cv
    cG
    cR
    cmulr
    cfv
    #
    co
    #
    wceq
    #
    va
    cB
    wrex
    #
    @7
    @3
    wceq
    #
    va
    cB
    wrex
    #
    @3
    @5
    wcel
    #
    @4
    @2
    @8
    @10
    va
    cB
    @8
    @10
    wb
    @2
    @3
    @7
    eqcom
    a1i
    rexbidv
    @0
    cR
    crglmod
    cfv
    #
    clmod
    wcel
    @1
    @12
    @9
    wb
    cR
    rlmlmod
    @6
    @3
    va
    cR
    cid
    cfv
    cB
    cK
    cB
    @13
    cG
    cR
    rlmsca2
    cR
    cbs
    cnx
    cbs
    cfv
    cB
    baseid
    rspsn.b
    strfvi
    cB
    cR
    cbs
    cfv
    @13
    cbs
    cfv
    rspsn.b
    cR
    rlmbas
    eqtri
    cR
    rlmvsca
    cK
    cR
    crsp
    cfv
    @13
    clspn
    cfv
    rspsn.k
    cR
    rspval
    eqtri
    lspsnel
    sylan
    @1
    @4
    @11
    wb
    @0
    va
    cB
    c.pa
    cR
    @6
    cG
    @3
    rspsn.b
    rspsn.d
    @6
    eqid
    dvdsr2
    adantl
    3bitr4d
    abbi2dv
end
