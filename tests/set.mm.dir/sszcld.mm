include "cz.mm"
include "wss.mm"
include "ccld.mm"
include "cfv.mm"
include "wcel.mm"
include "crest.mm"
include "co.mm"
include "zcld2.mm"
include "cdif.mm"
include "id.mm"
include "cpw.mm"
include "difss.mm"
include "zex.mm"
include "elpw2.mm"
include "mpbir.mm"
include "zdis.mm"
include "eleqtrri.mm"
include "a1i.mm"
include "ctop.mm"
include "wa.mm"
include "wb.mm"
include "cc.mm"
include "ctopon.mm"
include "cnfldtopon.mm"
include "zsscn.mm"
include "resttopon.mm"
include "mp2an.mm"
include "topontopi.mm"
include "toponunii.mm"
include "iscld.mm"
include "ax-mp.mm"
include "sylanbrc.mm"
include "restcldr.mm"
include "sylancr.mm"

theorem sszcld
  let cA: class A
  let cJ: class J
  let vn: setvar n
  let vr: setvar r
  let vu: setvar u
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vv: setvar v
  let cS: class S
  assume recld2.1: |- J = ( TopOpen ` CCfld )


  assert |- ( A C_ ZZ -> A e. ( Clsd ` J ) )

  proof
    cA
    cz
    wss
    #
    cz
    cJ
    ccld
    cfv
    #
    wcel
    cA
    cJ
    cz
    crest
    co
    #
    ccld
    cfv
    wcel
    #
    cA
    @1
    wcel
    cJ
    recld2.1
    zcld2
    @0
    @0
    cz
    cA
    cdif
    #
    @2
    wcel
    #
    @3
    @0
    id
    @5
    @0
    @4
    cz
    cpw
    #
    @2
    @4
    @6
    wcel
    @4
    cz
    wss
    cz
    cA
    difss
    @4
    cz
    zex
    elpw2
    mpbir
    cJ
    recld2.1
    zdis
    eleqtrri
    a1i
    @2
    ctop
    wcel
    @3
    @0
    @5
    wa
    wb
    cz
    @2
    cJ
    cc
    ctopon
    cfv
    wcel
    cz
    cc
    wss
    @2
    cz
    ctopon
    cfv
    wcel
    cJ
    recld2.1
    cnfldtopon
    zsscn
    cz
    cJ
    cc
    resttopon
    mp2an
    #
    topontopi
    cA
    @2
    cz
    cz
    @2
    @7
    toponunii
    iscld
    ax-mp
    sylanbrc
    cz
    cA
    cJ
    restcldr
    sylancr
end
