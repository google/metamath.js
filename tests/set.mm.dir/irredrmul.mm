include "crg.mm"
include "wcel.mm"
include "w3a.mm"
include "co.mm"
include "simp2.mm"
include "cv.mm"
include "wceq.mm"
include "cbs.mm"
include "cfv.mm"
include "cdif.mm"
include "wrex.mm"
include "wo.mm"
include "wn.mm"
include "cdvr.mm"
include "wi.mm"
include "simp1.mm"
include "simp3.mm"
include "eqid.mm"
include "unitdvcl.mm"
include "3com23.mm"
include "3expia.mm"
include "syl2anc.mm"
include "irredcl.mm"
include "3ad2ant2.mm"
include "dvrcan3.mm"
include "syl3anc.mm"
include "eleq1d.mm"
include "sylibd.mm"
include "wa.mm"
include "ad2antrr.mm"
include "eldifi.mm"
include "ad2antrl.mm"
include "dvrcl.mm"
include "eldifn.mm"
include "unitmulcl.mm"
include "dvrcan1.mm"
include "mtod.mm"
include "eldifd.mm"
include "simprr.mm"
include "oveq1d.mm"
include "ad2antlr.mm"
include "dvrass.mm"
include "syl13anc.mm"
include "3eqtr3d.mm"
include "oveq2.mm"
include "eqeq1d.mm"
include "rspcev.mm"
include "rexlimdvaa.mm"
include "reximdva.mm"
include "orim12d.mm"
include "wb.mm"
include "unitcl.mm"
include "3ad2ant3.mm"
include "ringcl.mm"
include "isnirred.mm"
include "syl.mm"
include "3imtr4d.mm"
include "mt4d.mm"

theorem irredrmul
  let cR: class R
  let c.x: class .x.
  let cU: class U
  let cI: class I
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cB: class B
  let c.0: class .0.
  assume irredn0.i: |- I = ( Irred ` R )
  assume irredrmul.u: |- U = ( Unit ` R )
  assume irredrmul.t: |- .x. = ( .r ` R )


  assert |- ( ( R e. Ring /\ X e. I /\ Y e. U ) -> ( X .x. Y ) e. I )

  proof
    cR
    crg
    wcel
    #
    cX
    cI
    wcel
    #
    cY
    cU
    wcel
    #
    w3a
    #
    @1
    cX
    cY
    c.x
    co
    #
    cI
    wcel
    #
    @0
    @1
    @2
    simp2
    @3
    @4
    cU
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    c.x
    co
    #
    @4
    wceq
    #
    vy
    cR
    cbs
    cfv
    #
    cU
    cdif
    #
    wrex
    #
    vx
    @12
    wrex
    #
    wo
    #
    cX
    cU
    wcel
    #
    @7
    vz
    cv
    #
    c.x
    co
    #
    cX
    wceq
    #
    vz
    @12
    wrex
    #
    vx
    @12
    wrex
    #
    wo
    #
    @5
    wn
    #
    @1
    wn
    #
    @3
    @6
    @16
    @14
    @21
    @3
    @6
    @4
    cY
    cR
    cdvr
    cfv
    #
    co
    #
    cU
    wcel
    #
    @16
    @3
    @0
    @2
    @6
    @27
    wi
    @0
    @1
    @2
    simp1
    #
    @0
    @1
    @2
    simp3
    #
    @0
    @2
    @6
    @27
    @0
    @6
    @2
    @27
    @25
    cR
    cU
    @4
    cY
    irredrmul.u
    @25
    eqid
    #
    unitdvcl
    3com23
    3expia
    syl2anc
    @3
    @26
    cX
    cU
    @3
    @0
    cX
    @11
    wcel
    #
    @2
    @26
    cX
    wceq
    #
    @28
    @1
    @0
    @31
    @2
    @11
    cR
    cI
    cX
    irredn0.i
    @11
    eqid
    #
    irredcl
    3ad2ant2
    #
    @29
    @11
    @25
    cR
    c.x
    cU
    cX
    cY
    @33
    irredrmul.u
    @30
    irredrmul.t
    dvrcan3
    syl3anc
    #
    eleq1d
    sylibd
    @3
    @13
    @20
    vx
    @12
    @3
    @7
    @12
    wcel
    #
    wa
    #
    @10
    @20
    vy
    @12
    @37
    @8
    @12
    wcel
    #
    @10
    wa
    #
    wa
    #
    @8
    cY
    @25
    co
    #
    @12
    wcel
    @7
    @41
    c.x
    co
    #
    cX
    wceq
    #
    @20
    @40
    @41
    @11
    cU
    @40
    @0
    @8
    @11
    wcel
    #
    @2
    @41
    @11
    wcel
    @3
    @0
    @36
    @39
    @28
    ad2antrr
    #
    @38
    @44
    @37
    @10
    @8
    @11
    cU
    eldifi
    ad2antrl
    #
    @3
    @2
    @36
    @39
    @29
    ad2antrr
    #
    @11
    @25
    cR
    cU
    @8
    cY
    @33
    irredrmul.u
    @30
    dvrcl
    syl3anc
    @40
    @41
    cU
    wcel
    #
    @8
    cU
    wcel
    #
    @38
    @49
    wn
    @37
    @10
    @8
    @11
    cU
    eldifn
    ad2antrl
    @40
    @48
    @41
    cY
    c.x
    co
    #
    cU
    wcel
    #
    @49
    @40
    @0
    @2
    @48
    @51
    wi
    @45
    @47
    @0
    @2
    @48
    @51
    @0
    @48
    @2
    @51
    cR
    c.x
    cU
    @41
    cY
    irredrmul.u
    irredrmul.t
    unitmulcl
    3com23
    3expia
    syl2anc
    @40
    @50
    @8
    cU
    @40
    @0
    @44
    @2
    @50
    @8
    wceq
    @45
    @46
    @47
    @11
    @25
    cR
    c.x
    cU
    @8
    cY
    @33
    irredrmul.u
    @30
    irredrmul.t
    dvrcan1
    syl3anc
    eleq1d
    sylibd
    mtod
    eldifd
    @40
    @9
    cY
    @25
    co
    #
    @26
    @42
    cX
    @40
    @9
    @4
    cY
    @25
    @37
    @38
    @10
    simprr
    oveq1d
    @40
    @0
    @7
    @11
    wcel
    #
    @44
    @2
    @52
    @42
    wceq
    @45
    @36
    @53
    @3
    @39
    @7
    @11
    cU
    eldifi
    ad2antlr
    @46
    @47
    @11
    @25
    cR
    c.x
    cU
    @7
    @8
    cY
    @33
    irredrmul.u
    @30
    irredrmul.t
    dvrass
    syl13anc
    @3
    @32
    @36
    @39
    @35
    ad2antrr
    3eqtr3d
    @19
    @43
    vz
    @41
    @12
    @17
    @41
    wceq
    @18
    @42
    cX
    @17
    @41
    @7
    c.x
    oveq2
    eqeq1d
    rspcev
    syl2anc
    rexlimdvaa
    reximdva
    orim12d
    @3
    @4
    @11
    wcel
    #
    @23
    @15
    wb
    @3
    @0
    @31
    cY
    @11
    wcel
    #
    @54
    @28
    @34
    @2
    @0
    @55
    @1
    @11
    cR
    cU
    cY
    @33
    irredrmul.u
    unitcl
    3ad2ant3
    @11
    cR
    c.x
    cX
    cY
    @33
    irredrmul.t
    ringcl
    syl3anc
    vx
    vy
    @11
    cR
    c.x
    cU
    cI
    @12
    @4
    @33
    irredrmul.u
    irredn0.i
    @12
    eqid
    #
    irredrmul.t
    isnirred
    syl
    @3
    @31
    @24
    @22
    wb
    @34
    vx
    vz
    @11
    cR
    c.x
    cU
    cI
    @12
    cX
    @33
    irredrmul.u
    irredn0.i
    @56
    irredrmul.t
    isnirred
    syl
    3imtr4d
    mt4d
end
