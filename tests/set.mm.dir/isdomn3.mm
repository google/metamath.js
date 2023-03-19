include "cdomn.mm"
include "wcel.mm"
include "cnzr.mm"
include "cv.mm"
include "cmulr.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "wo.mm"
include "wi.mm"
include "wral.mm"
include "wa.mm"
include "crg.mm"
include "csn.mm"
include "cdif.mm"
include "csubmnd.mm"
include "eqid.mm"
include "isdomn.mm"
include "cur.mm"
include "wne.mm"
include "isnzr.mm"
include "anbi1i.mm"
include "anass.mm"
include "bitri.mm"
include "wb.mm"
include "ringidcl.mm"
include "eldifsn.mm"
include "baibr.mm"
include "syl.mm"
include "ringcl.mm"
include "3expb.mm"
include "biantrurd.mm"
include "syl6bbr.mm"
include "imbi2d.mm"
include "2ralbidva.mm"
include "wn.mm"
include "con34b.mm"
include "neanior.mm"
include "df-ne.mm"
include "imbi12i.mm"
include "bitr4i.mm"
include "2ralbii.mm"
include "wal.mm"
include "impexp.mm"
include "an4.mm"
include "anbi12i.mm"
include "imbi1i.mm"
include "bitr3i.mm"
include "2albii.mm"
include "r2al.mm"
include "3bitr4ri.mm"
include "3bitr4g.mm"
include "anbi12d.mm"
include "cmnd.mm"
include "ringmgp.mm"
include "wss.mm"
include "w3a.mm"
include "mgpbas.mm"
include "ringidval.mm"
include "mgpplusg.mm"
include "issubm.mm"
include "3anass.mm"
include "syl6bb.mm"
include "difss.mm"
include "biantrur.mm"
include "bitr4d.mm"
include "pm5.32i.mm"

theorem isdomn3
  let cB: class B
  let cR: class R
  let cU: class U
  let c.0: class .0.
  let vx: setvar x
  let vy: setvar y
  assume isdomn3.b: |- B = ( Base ` R )
  assume isdomn3.z: |- .0. = ( 0g ` R )
  assume isdomn3.u: |- U = ( mulGrp ` R )


  assert |- ( R e. Domn <-> ( R e. Ring /\ ( B \ { .0. } ) e. ( SubMnd ` U ) ) )

  proof
    cR
    cdomn
    wcel
    cR
    cnzr
    wcel
    #
    vx
    cv
    #
    vy
    cv
    #
    cR
    cmulr
    cfv
    #
    co
    #
    c.0
    wceq
    #
    @1
    c.0
    wceq
    @2
    c.0
    wceq
    wo
    #
    wi
    #
    vy
    cB
    wral
    vx
    cB
    wral
    #
    wa
    #
    cR
    crg
    wcel
    #
    cB
    c.0
    csn
    #
    cdif
    #
    cU
    csubmnd
    cfv
    wcel
    #
    wa
    #
    vx
    vy
    cB
    cR
    @3
    c.0
    isdomn3.b
    @3
    eqid
    #
    isdomn3.z
    isdomn
    @9
    @10
    cR
    cur
    cfv
    #
    c.0
    wne
    #
    @8
    wa
    #
    wa
    #
    @14
    @9
    @10
    @17
    wa
    #
    @8
    wa
    @19
    @0
    @20
    @8
    cR
    @16
    c.0
    @16
    eqid
    #
    isdomn3.z
    isnzr
    anbi1i
    @10
    @17
    @8
    anass
    bitri
    @10
    @18
    @13
    @10
    @18
    @16
    @12
    wcel
    #
    @4
    @12
    wcel
    #
    vy
    @12
    wral
    vx
    @12
    wral
    #
    wa
    #
    @13
    @10
    @17
    @22
    @8
    @24
    @10
    @16
    cB
    wcel
    #
    @17
    @22
    wb
    cB
    cR
    @16
    isdomn3.b
    @21
    ringidcl
    @22
    @26
    @17
    @16
    cB
    c.0
    eldifsn
    baibr
    syl
    @10
    @1
    c.0
    wne
    #
    @2
    c.0
    wne
    #
    wa
    #
    @4
    c.0
    wne
    #
    wi
    #
    vy
    cB
    wral
    vx
    cB
    wral
    @29
    @23
    wi
    #
    vy
    cB
    wral
    vx
    cB
    wral
    #
    @8
    @24
    @10
    @31
    @32
    vx
    vy
    cB
    cB
    @10
    @1
    cB
    wcel
    #
    @2
    cB
    wcel
    #
    wa
    #
    wa
    #
    @30
    @23
    @29
    @37
    @30
    @4
    cB
    wcel
    #
    @30
    wa
    @23
    @37
    @38
    @30
    @10
    @34
    @35
    @38
    cB
    cR
    @3
    @1
    @2
    isdomn3.b
    @15
    ringcl
    3expb
    biantrurd
    @4
    cB
    c.0
    eldifsn
    syl6bbr
    imbi2d
    2ralbidva
    @7
    @31
    vx
    vy
    cB
    cB
    @7
    @6
    wn
    #
    @5
    wn
    #
    wi
    @31
    @5
    @6
    con34b
    @29
    @39
    @30
    @40
    @1
    c.0
    @2
    c.0
    neanior
    @4
    c.0
    df-ne
    imbi12i
    bitr4i
    2ralbii
    @36
    @32
    wi
    #
    vy
    wal
    vx
    wal
    @1
    @12
    wcel
    #
    @2
    @12
    wcel
    #
    wa
    #
    @23
    wi
    #
    vy
    wal
    vx
    wal
    @33
    @24
    @41
    @45
    vx
    vy
    @41
    @36
    @29
    wa
    #
    @23
    wi
    @45
    @36
    @29
    @23
    impexp
    @46
    @44
    @23
    @46
    @34
    @27
    wa
    #
    @35
    @28
    wa
    #
    wa
    @44
    @34
    @35
    @27
    @28
    an4
    @42
    @47
    @43
    @48
    @1
    cB
    c.0
    eldifsn
    @2
    cB
    c.0
    eldifsn
    anbi12i
    bitr4i
    imbi1i
    bitr3i
    2albii
    @32
    vx
    vy
    cB
    cB
    r2al
    @23
    vx
    vy
    @12
    @12
    r2al
    3bitr4ri
    3bitr4g
    anbi12d
    @10
    cU
    cmnd
    wcel
    #
    @13
    @25
    wb
    cR
    cU
    isdomn3.u
    ringmgp
    @49
    @13
    @12
    cB
    wss
    #
    @25
    wa
    #
    @25
    @49
    @13
    @50
    @22
    @24
    w3a
    @51
    vx
    vy
    cB
    @3
    @12
    cU
    @16
    cB
    cR
    cU
    isdomn3.u
    isdomn3.b
    mgpbas
    cR
    @16
    cU
    isdomn3.u
    @21
    ringidval
    cR
    @3
    cU
    isdomn3.u
    @15
    mgpplusg
    issubm
    @50
    @22
    @24
    3anass
    syl6bb
    @50
    @25
    cB
    @11
    difss
    biantrur
    syl6bbr
    syl
    bitr4d
    pm5.32i
    bitri
    bitri
end
