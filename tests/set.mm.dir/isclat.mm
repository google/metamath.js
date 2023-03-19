include "cv.mm"
include "club.mm"
include "cfv.mm"
include "cdm.mm"
include "cbs.mm"
include "cpw.mm"
include "wceq.mm"
include "cglb.mm"
include "wa.mm"
include "cpo.mm"
include "ccla.mm"
include "fveq2.mm"
include "syl6eqr.mm"
include "dmeqd.mm"
include "pweqd.mm"
include "eqeq12d.mm"
include "anbi12d.mm"
include "df-clat.mm"
include "elrab2.mm"

theorem isclat
  let cB: class B
  let cU: class U
  let cG: class G
  let cK: class K
  let vl: setvar l
  assume isclat.b: |- B = ( Base ` K )
  assume isclat.u: |- U = ( lub ` K )
  assume isclat.g: |- G = ( glb ` K )


  assert |- ( K e. CLat <-> ( K e. Poset /\ ( dom U = ~P B /\ dom G = ~P B ) ) )

  proof
    vl
    cv
    #
    club
    cfv
    #
    cdm
    #
    @0
    cbs
    cfv
    #
    cpw
    #
    wceq
    #
    @0
    cglb
    cfv
    #
    cdm
    #
    @4
    wceq
    #
    wa
    cU
    cdm
    #
    cB
    cpw
    #
    wceq
    #
    cG
    cdm
    #
    @10
    wceq
    #
    wa
    vl
    cK
    cpo
    ccla
    @0
    cK
    wceq
    #
    @5
    @11
    @8
    @13
    @14
    @2
    @9
    @4
    @10
    @14
    @1
    cU
    @14
    @1
    cK
    club
    cfv
    cU
    @0
    cK
    club
    fveq2
    isclat.u
    syl6eqr
    dmeqd
    @14
    @3
    cB
    @14
    @3
    cK
    cbs
    cfv
    cB
    @0
    cK
    cbs
    fveq2
    isclat.b
    syl6eqr
    pweqd
    #
    eqeq12d
    @14
    @7
    @12
    @4
    @10
    @14
    @6
    cG
    @14
    @6
    cK
    cglb
    cfv
    cG
    @0
    cK
    cglb
    fveq2
    isclat.g
    syl6eqr
    dmeqd
    @15
    eqeq12d
    anbi12d
    vl
    df-clat
    elrab2
end
