include "cxmt.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cr.mm"
include "c2.mm"
include "cdiv.mm"
include "co.mm"
include "cbl.mm"
include "cmin.mm"
include "cle.mm"
include "wbr.mm"
include "wss.mm"
include "simpll.mm"
include "simplr.mm"
include "clt.mm"
include "simprr.mm"
include "cxr.mm"
include "wb.mm"
include "simprl.mm"
include "rehalfcld.mm"
include "rexrd.mm"
include "elbl.mm"
include "syl3anc.mm"
include "mpbid.mm"
include "simpld.mm"
include "simprd.mm"
include "wi.mm"
include "xmetcl.mm"
include "xrltle.mm"
include "syl2anc.mm"
include "mpd.mm"
include "caddc.mm"
include "recnd.mm"
include "pncand.mm"
include "2halvesd.mm"
include "oveq1d.mm"
include "eqtr3d.mm"
include "breqtrd.mm"
include "blss2.mm"
include "syl33anc.mm"

theorem blhalf
  let cR: class R
  let cM: class M
  let cX: class X
  let cY: class Y
  let cZ: class Z


  assert |- ( ( ( M e. ( *Met ` X ) /\ Y e. X ) /\ ( R e. RR /\ Z e. ( Y ( ball ` M ) ( R / 2 ) ) ) ) -> ( Y ( ball ` M ) ( R / 2 ) ) C_ ( Z ( ball ` M ) R ) )

  proof
    cM
    cX
    cxmt
    cfv
    wcel
    #
    cY
    cX
    wcel
    #
    wa
    #
    cR
    cr
    wcel
    #
    cZ
    cY
    cR
    c2
    cdiv
    co
    #
    cM
    cbl
    cfv
    #
    co
    #
    wcel
    #
    wa
    #
    wa
    #
    @0
    @1
    cZ
    cX
    wcel
    #
    @4
    cr
    wcel
    @3
    cY
    cZ
    cM
    co
    #
    cR
    @4
    cmin
    co
    #
    cle
    wbr
    @6
    cZ
    cR
    @5
    co
    wss
    @0
    @1
    @8
    simpll
    #
    @0
    @1
    @8
    simplr
    #
    @9
    @10
    @11
    @4
    clt
    wbr
    #
    @9
    @7
    @10
    @15
    wa
    #
    @2
    @3
    @7
    simprr
    @9
    @0
    @1
    @4
    cxr
    wcel
    #
    @7
    @16
    wb
    @13
    @14
    @9
    @4
    @9
    cR
    @2
    @3
    @7
    simprl
    #
    rehalfcld
    #
    rexrd
    #
    cZ
    cM
    cY
    @4
    cX
    elbl
    syl3anc
    mpbid
    #
    simpld
    #
    @19
    @18
    @9
    @11
    @4
    @12
    cle
    @9
    @15
    @11
    @4
    cle
    wbr
    #
    @9
    @10
    @15
    @21
    simprd
    @9
    @11
    cxr
    wcel
    #
    @17
    @15
    @23
    wi
    @9
    @0
    @1
    @10
    @24
    @13
    @14
    @22
    cY
    cZ
    cM
    cX
    xmetcl
    syl3anc
    @20
    @11
    @4
    xrltle
    syl2anc
    mpd
    @9
    @4
    @4
    caddc
    co
    #
    @4
    cmin
    co
    @4
    @12
    @9
    @4
    @4
    @9
    @4
    @19
    recnd
    #
    @26
    pncand
    @9
    @25
    cR
    @4
    cmin
    @9
    cR
    @9
    cR
    @18
    recnd
    2halvesd
    oveq1d
    eqtr3d
    breqtrd
    cM
    cY
    cZ
    @4
    cR
    cX
    blss2
    syl33anc
end
