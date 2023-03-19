include "wcel.mm"
include "wa.mm"
include "cc0.mm"
include "crelexp.mm"
include "co.mm"
include "wceq.mm"
include "cid.mm"
include "cdm.mm"
include "crn.mm"
include "cun.mm"
include "cres.mm"
include "relexp0g.mm"
include "eqeqan12d.mm"
include "cv.mm"
include "weq.mm"
include "wb.mm"
include "wal.mm"
include "copab.mm"
include "dfcleq.mm"
include "alcom.mm"
include "19.3v.mm"
include "wi.mm"
include "wex.mm"
include "ax6ev.mm"
include "pm5.5.mm"
include "ax-mp.mm"
include "19.23v.mm"
include "3bitr4ri.mm"
include "pm5.32.mm"
include "ancom.mm"
include "bibi12i.mm"
include "bitri.mm"
include "albii.mm"
include "3bitr3i.mm"
include "eqopab2b.mm"
include "opabresid.mm"
include "eqeq12i.mm"
include "3bitr2i.mm"
include "syl6rbbr.mm"

theorem relexp0eq
  let cA: class A
  let cB: class B
  let cU: class U
  let cV: class V
  let vx: setvar x
  let vy: setvar y


  assert |- ( ( A e. U /\ B e. V ) -> ( ( dom A u. ran A ) = ( dom B u. ran B ) <-> ( A ^r 0 ) = ( B ^r 0 ) ) )

  proof
    cA
    cU
    wcel
    #
    cB
    cV
    wcel
    #
    wa
    cA
    cc0
    crelexp
    co
    #
    cB
    cc0
    crelexp
    co
    #
    wceq
    cid
    cA
    cdm
    cA
    crn
    cun
    #
    cres
    #
    cid
    cB
    cdm
    cB
    crn
    cun
    #
    cres
    #
    wceq
    #
    @4
    @6
    wceq
    #
    @0
    @1
    @2
    @5
    @3
    @7
    cA
    cU
    relexp0g
    cB
    cV
    relexp0g
    eqeqan12d
    @9
    vx
    cv
    #
    @4
    wcel
    #
    vy
    vx
    weq
    #
    wa
    #
    @10
    @6
    wcel
    #
    @12
    wa
    #
    wb
    #
    vy
    wal
    #
    vx
    wal
    #
    @13
    vx
    vy
    copab
    #
    @15
    vx
    vy
    copab
    #
    wceq
    @8
    @9
    @11
    @14
    wb
    #
    vx
    wal
    #
    @18
    vx
    @4
    @6
    dfcleq
    @22
    vy
    wal
    @21
    vy
    wal
    #
    vx
    wal
    @22
    @18
    @21
    vy
    vx
    alcom
    @22
    vy
    19.3v
    @23
    @17
    vx
    @23
    @12
    @21
    wi
    #
    vy
    wal
    #
    @17
    @12
    vy
    wex
    #
    @21
    wi
    #
    @21
    @25
    @23
    @26
    @27
    @21
    wb
    vy
    vx
    ax6ev
    @26
    @21
    pm5.5
    ax-mp
    @12
    @21
    vy
    19.23v
    @21
    vy
    19.3v
    3bitr4ri
    @24
    @16
    vy
    @24
    @12
    @11
    wa
    #
    @12
    @14
    wa
    #
    wb
    @16
    @12
    @11
    @14
    pm5.32
    @28
    @13
    @29
    @15
    @12
    @11
    ancom
    @12
    @14
    ancom
    bibi12i
    bitri
    albii
    bitri
    albii
    3bitr3i
    bitri
    @13
    @15
    vx
    vy
    eqopab2b
    @19
    @5
    @20
    @7
    vx
    vy
    @4
    opabresid
    vx
    vy
    @6
    opabresid
    eqeq12i
    3bitr2i
    syl6rbbr
end
