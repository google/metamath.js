include "cmnd.mm"
include "wcel.mm"
include "cn0.mm"
include "w3a.mm"
include "cfv.mm"
include "cn.mm"
include "cdvds.mm"
include "wbr.mm"
include "co.mm"
include "wceq.mm"
include "wb.mm"
include "cc0.mm"
include "cmin.mm"
include "wi.mm"
include "wa.mm"
include "0nn0.mm"
include "mndodcong.mm"
include "3expia.mm"
include "mpanr2.mm"
include "3impa.mm"
include "cc.mm"
include "nn0cn.mm"
include "3ad2ant3.mm"
include "subid1d.mm"
include "breq2d.mm"
include "mulg0.mm"
include "3ad2ant2.mm"
include "eqeq2d.mm"
include "bibi12d.mm"
include "sylibd.mm"
include "simpr.mm"
include "breq1d.mm"
include "cz.mm"
include "simpl3.mm"
include "nn0z.mm"
include "0dvds.mm"
include "3syl.mm"
include "adantr.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "syl5ibrcom.mm"
include "wn.mm"
include "wne.mm"
include "c1.mm"
include "cfz.mm"
include "odlem2.mm"
include "3com23.mm"
include "elfznn.mm"
include "nnne0.mm"
include "3ad2antl2.mm"
include "necon2bd.mm"
include "wo.mm"
include "elnn0.mm"
include "sylib.mm"
include "ord.mm"
include "syld.mm"
include "impancom.mm"
include "impbid.mm"
include "3bitrd.mm"
include "ex.mm"
include "odcl.mm"
include "mpjaod.mm"

theorem oddvdsnn0
  let cA: class A
  let c.x: class .x.
  let cG: class G
  let cN: class N
  let cO: class O
  let cX: class X
  let c.0: class .0.
  let vw: setvar w
  let vy: setvar y
  let vz: setvar z
  let vx: setvar x
  assume odcl.1: |- X = ( Base ` G )
  assume odcl.2: |- O = ( od ` G )
  assume odid.3: |- .x. = ( .g ` G )
  assume odid.4: |- .0. = ( 0g ` G )


  assert |- ( ( G e. Mnd /\ A e. X /\ N e. NN0 ) -> ( ( O ` A ) || N <-> ( N .x. A ) = .0. ) )

  proof
    cG
    cmnd
    wcel
    #
    cA
    cX
    wcel
    #
    cN
    cn0
    wcel
    #
    w3a
    #
    cA
    cO
    cfv
    #
    cn
    wcel
    #
    @4
    cN
    cdvds
    wbr
    #
    cN
    cA
    c.x
    co
    #
    c.0
    wceq
    #
    wb
    #
    @4
    cc0
    wceq
    #
    @3
    @5
    @4
    cN
    cc0
    cmin
    co
    #
    cdvds
    wbr
    #
    @7
    cc0
    cA
    c.x
    co
    #
    wceq
    #
    wb
    #
    @9
    @0
    @1
    @2
    @5
    @15
    wi
    #
    @0
    @1
    wa
    #
    @2
    cc0
    cn0
    wcel
    #
    @16
    0nn0
    @17
    @2
    @18
    wa
    @5
    @15
    cA
    c.x
    cG
    cN
    cc0
    cO
    cX
    c.0
    odcl.1
    odcl.2
    odid.3
    odid.4
    mndodcong
    3expia
    mpanr2
    3impa
    @3
    @12
    @6
    @14
    @8
    @3
    @11
    cN
    @4
    cdvds
    @3
    cN
    @2
    @0
    cN
    cc
    wcel
    @1
    cN
    nn0cn
    3ad2ant3
    subid1d
    breq2d
    @3
    @13
    c.0
    @7
    @1
    @0
    @13
    c.0
    wceq
    #
    @2
    cX
    c.x
    cG
    cA
    c.0
    odcl.1
    odid.4
    odid.3
    mulg0
    3ad2ant2
    #
    eqeq2d
    bibi12d
    sylibd
    @3
    @10
    @9
    @3
    @10
    wa
    #
    @6
    cc0
    cN
    cdvds
    wbr
    #
    cN
    cc0
    wceq
    #
    @8
    @21
    @4
    cc0
    cN
    cdvds
    @3
    @10
    simpr
    breq1d
    @21
    @2
    cN
    cz
    wcel
    @22
    @23
    wb
    @0
    @1
    @2
    @10
    simpl3
    cN
    nn0z
    cN
    0dvds
    3syl
    @21
    @23
    @8
    @21
    @8
    @23
    @19
    @3
    @19
    @10
    @20
    adantr
    @23
    @7
    @13
    c.0
    cN
    cc0
    cA
    c.x
    oveq1
    eqeq1d
    syl5ibrcom
    @3
    @8
    @10
    @23
    @3
    @8
    wa
    #
    @10
    cN
    cn
    wcel
    #
    wn
    @23
    @24
    @25
    @4
    cc0
    @1
    @0
    @8
    @25
    @4
    cc0
    wne
    #
    wi
    @2
    @1
    @8
    @25
    @26
    @1
    @8
    @25
    w3a
    @4
    c1
    cN
    cfz
    co
    wcel
    #
    @5
    @26
    @1
    @25
    @8
    @27
    cA
    c.x
    cG
    cN
    cO
    cX
    c.0
    odcl.1
    odcl.2
    odid.3
    odid.4
    odlem2
    3com23
    @4
    cN
    elfznn
    @4
    nnne0
    3syl
    3expia
    3ad2antl2
    necon2bd
    @24
    @25
    @23
    @24
    @2
    @25
    @23
    wo
    @0
    @1
    @2
    @8
    simpl3
    cN
    elnn0
    sylib
    ord
    syld
    impancom
    impbid
    3bitrd
    ex
    @3
    @4
    cn0
    wcel
    #
    @5
    @10
    wo
    @1
    @0
    @28
    @2
    cA
    cG
    cO
    cX
    odcl.1
    odcl.2
    odcl
    3ad2ant2
    @4
    elnn0
    sylib
    mpjaod
end
