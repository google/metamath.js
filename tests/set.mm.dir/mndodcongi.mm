include "cmnd.mm"
include "wcel.mm"
include "cn0.mm"
include "wa.mm"
include "w3a.mm"
include "cfv.mm"
include "cn.mm"
include "cmin.mm"
include "co.mm"
include "cdvds.mm"
include "wbr.mm"
include "wceq.mm"
include "wi.mm"
include "cc0.mm"
include "mndodcong.mm"
include "biimpd.mm"
include "3expia.mm"
include "3impa.mm"
include "cz.mm"
include "wb.mm"
include "nn0z.mm"
include "zsubcl.mm"
include "syl2an.mm"
include "3ad2ant3.mm"
include "0dvds.mm"
include "syl.mm"
include "cc.mm"
include "nn0cn.mm"
include "subeq0.mm"
include "oveq1.mm"
include "syl6bi.mm"
include "sylbid.mm"
include "breq1.mm"
include "imbi1d.mm"
include "syl5ibrcom.mm"
include "wo.mm"
include "odcl.mm"
include "3ad2ant2.mm"
include "elnn0.mm"
include "sylib.mm"
include "mpjaod.mm"

theorem mndodcongi
  let cA: class A
  let c.x: class .x.
  let cG: class G
  let cM: class M
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


  assert |- ( ( G e. Mnd /\ A e. X /\ ( M e. NN0 /\ N e. NN0 ) ) -> ( ( O ` A ) || ( M - N ) -> ( M .x. A ) = ( N .x. A ) ) )

  proof
    cG
    cmnd
    wcel
    #
    cA
    cX
    wcel
    #
    cM
    cn0
    wcel
    #
    cN
    cn0
    wcel
    #
    wa
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
    @6
    cM
    cN
    cmin
    co
    #
    cdvds
    wbr
    #
    cM
    cA
    c.x
    co
    cN
    cA
    c.x
    co
    wceq
    #
    wi
    #
    @6
    cc0
    wceq
    #
    @0
    @1
    @4
    @7
    @11
    wi
    @0
    @1
    wa
    #
    @4
    @7
    @11
    @13
    @4
    @7
    w3a
    @9
    @10
    cA
    c.x
    cG
    cM
    cN
    cO
    cX
    c.0
    odcl.1
    odcl.2
    odid.3
    odid.4
    mndodcong
    biimpd
    3expia
    3impa
    @5
    @11
    @12
    cc0
    @8
    cdvds
    wbr
    #
    @10
    wi
    @5
    @14
    @8
    cc0
    wceq
    #
    @10
    @5
    @8
    cz
    wcel
    #
    @14
    @15
    wb
    @4
    @0
    @16
    @1
    @2
    cM
    cz
    wcel
    cN
    cz
    wcel
    @16
    @3
    cM
    nn0z
    cN
    nn0z
    cM
    cN
    zsubcl
    syl2an
    3ad2ant3
    @8
    0dvds
    syl
    @5
    @15
    cM
    cN
    wceq
    #
    @10
    @4
    @0
    @15
    @17
    wb
    #
    @1
    @2
    cM
    cc
    wcel
    cN
    cc
    wcel
    @18
    @3
    cM
    nn0cn
    cN
    nn0cn
    cM
    cN
    subeq0
    syl2an
    3ad2ant3
    cM
    cN
    cA
    c.x
    oveq1
    syl6bi
    sylbid
    @12
    @9
    @14
    @10
    @6
    cc0
    @8
    cdvds
    breq1
    imbi1d
    syl5ibrcom
    @5
    @6
    cn0
    wcel
    #
    @7
    @12
    wo
    @1
    @0
    @19
    @4
    cA
    cG
    cO
    cX
    odcl.1
    odcl.2
    odcl
    3ad2ant2
    @6
    elnn0
    sylib
    mpjaod
end
