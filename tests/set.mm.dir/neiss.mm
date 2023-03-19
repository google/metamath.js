include "ctop.mm"
include "wcel.mm"
include "cnei.mm"
include "cfv.mm"
include "wss.mm"
include "w3a.mm"
include "cuni.mm"
include "cv.mm"
include "wa.mm"
include "wrex.mm"
include "eqid.mm"
include "neii1.mm"
include "3adant3.mm"
include "neii2.mm"
include "wi.mm"
include "sstr2.mm"
include "anim1d.mm"
include "reximdv.mm"
include "3ad2ant3.mm"
include "mpd.mm"
include "wb.mm"
include "simp1.mm"
include "simp3.mm"
include "neiss2.mm"
include "sstrd.mm"
include "isnei.mm"
include "syl2anc.mm"
include "mpbir2and.mm"

theorem neiss
  let cR: class R
  let cS: class S
  let cJ: class J
  let cN: class N
  let vg: setvar g


  assert |- ( ( J e. Top /\ N e. ( ( nei ` J ) ` S ) /\ R C_ S ) -> N e. ( ( nei ` J ) ` R ) )

  proof
    cJ
    ctop
    wcel
    #
    cN
    cS
    cJ
    cnei
    cfv
    #
    cfv
    wcel
    #
    cR
    cS
    wss
    #
    w3a
    #
    cN
    cR
    @1
    cfv
    wcel
    #
    cN
    cJ
    cuni
    #
    wss
    #
    cR
    vg
    cv
    #
    wss
    #
    @8
    cN
    wss
    #
    wa
    #
    vg
    cJ
    wrex
    #
    @0
    @2
    @7
    @3
    cS
    cJ
    cN
    @6
    @6
    eqid
    #
    neii1
    3adant3
    @4
    cS
    @8
    wss
    #
    @10
    wa
    #
    vg
    cJ
    wrex
    #
    @12
    @0
    @2
    @16
    @3
    cS
    vg
    cJ
    cN
    neii2
    3adant3
    @3
    @0
    @16
    @12
    wi
    @2
    @3
    @15
    @11
    vg
    cJ
    @3
    @14
    @9
    @10
    cR
    cS
    @8
    sstr2
    anim1d
    reximdv
    3ad2ant3
    mpd
    @4
    @0
    cR
    @6
    wss
    @5
    @7
    @12
    wa
    wb
    @0
    @2
    @3
    simp1
    @4
    cR
    cS
    @6
    @0
    @2
    @3
    simp3
    @0
    @2
    cS
    @6
    wss
    @3
    cS
    cJ
    cN
    @6
    @13
    neiss2
    3adant3
    sstrd
    cR
    vg
    cJ
    cN
    @6
    @13
    isnei
    syl2anc
    mpbir2and
end
