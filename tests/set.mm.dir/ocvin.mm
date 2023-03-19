include "cphl.mm"
include "wcel.mm"
include "wa.mm"
include "cfv.mm"
include "cin.mm"
include "csn.mm"
include "cv.mm"
include "wceq.mm"
include "cip.mm"
include "co.mm"
include "csca.mm"
include "c0g.mm"
include "cbs.mm"
include "eqid.mm"
include "ocvi.mm"
include "ancoms.mm"
include "adantl.mm"
include "wb.mm"
include "simpll.mm"
include "lssel.mm"
include "ad2ant2lr.mm"
include "ipeq0.mm"
include "syl2anc.mm"
include "mpbid.mm"
include "ex.mm"
include "elin.mm"
include "velsn.mm"
include "3imtr4g.mm"
include "ssrdv.mm"
include "clmod.mm"
include "wss.mm"
include "phllmod.mm"
include "adantr.mm"
include "lssss.mm"
include "ocvlss.mm"
include "sylan2.mm"
include "lssincl.mm"
include "syl3an1.mm"
include "mpd3an3.mm"
include "lss0ss.mm"
include "eqssd.mm"

theorem ocvin
  let cS: class S
  let cL: class L
  let c.pe: class ._|_
  let cW: class W
  let c.0: class .0.
  let vx: setvar x
  let vy: setvar y
  let cT: class T
  assume ocv2ss.o: |- ._|_ = ( ocv ` W )
  assume ocvin.l: |- L = ( LSubSp ` W )
  assume ocvin.z: |- .0. = ( 0g ` W )


  assert |- ( ( W e. PreHil /\ S e. L ) -> ( S i^i ( ._|_ ` S ) ) = { .0. } )

  proof
    cW
    cphl
    wcel
    #
    cS
    cL
    wcel
    #
    wa
    #
    cS
    cS
    c.pe
    cfv
    #
    cin
    #
    c.0
    csn
    #
    @2
    vx
    @4
    @5
    @2
    vx
    cv
    #
    cS
    wcel
    #
    @6
    @3
    wcel
    #
    wa
    #
    @6
    c.0
    wceq
    #
    @6
    @4
    wcel
    @6
    @5
    wcel
    @2
    @9
    @10
    @2
    @9
    wa
    #
    @6
    @6
    cW
    cip
    cfv
    #
    co
    cW
    csca
    cfv
    #
    c0g
    cfv
    #
    wceq
    #
    @10
    @9
    @15
    @2
    @8
    @7
    @15
    @6
    @6
    cS
    @13
    @12
    c.pe
    cW
    cbs
    cfv
    #
    cW
    @14
    @16
    eqid
    #
    @12
    eqid
    #
    @13
    eqid
    #
    @14
    eqid
    #
    ocv2ss.o
    ocvi
    ancoms
    adantl
    @11
    @0
    @6
    @16
    wcel
    #
    @15
    @10
    wb
    @0
    @1
    @9
    simpll
    @1
    @7
    @21
    @0
    @8
    cL
    cS
    @16
    cW
    @6
    @17
    ocvin.l
    lssel
    ad2ant2lr
    @6
    @13
    @12
    @16
    cW
    c.0
    @14
    @19
    @18
    @17
    @20
    ocvin.z
    ipeq0
    syl2anc
    mpbid
    ex
    @6
    cS
    @3
    elin
    vx
    c.0
    velsn
    3imtr4g
    ssrdv
    @2
    cW
    clmod
    wcel
    #
    @4
    cL
    wcel
    #
    @5
    @4
    wss
    @0
    @22
    @1
    cW
    phllmod
    #
    adantr
    @0
    @1
    @3
    cL
    wcel
    #
    @23
    @1
    @0
    cS
    @16
    wss
    @25
    cL
    cS
    @16
    cW
    @17
    ocvin.l
    lssss
    cS
    cL
    c.pe
    @16
    cW
    @17
    ocv2ss.o
    ocvin.l
    ocvlss
    sylan2
    @0
    @22
    @1
    @25
    @23
    @24
    cL
    cS
    @3
    cW
    ocvin.l
    lssincl
    syl3an1
    mpd3an3
    cL
    cW
    @4
    c.0
    ocvin.z
    ocvin.l
    lss0ss
    syl2anc
    eqssd
end
