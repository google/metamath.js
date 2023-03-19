include "cme.mm"
include "cfv.mm"
include "wcel.mm"
include "w3a.mm"
include "cr.mm"
include "co.mm"
include "c2.mm"
include "cdiv.mm"
include "cle.mm"
include "wbr.mm"
include "wa.mm"
include "cxmt.mm"
include "cxr.mm"
include "cxad.mm"
include "cbl.mm"
include "cin.mm"
include "c0.mm"
include "wceq.mm"
include "simpl1.mm"
include "metxmet.mm"
include "syl.mm"
include "simpl2.mm"
include "simpl3.mm"
include "rexr.mm"
include "ad2antrl.mm"
include "cmul.mm"
include "caddc.mm"
include "simprl.mm"
include "rexadd.mm"
include "syl2anc.mm"
include "recnd.mm"
include "2timesd.mm"
include "eqtr4d.mm"
include "wb.mm"
include "id.mm"
include "metcl.mm"
include "cc0.mm"
include "clt.mm"
include "2re.mm"
include "2pos.mm"
include "pm3.2i.mm"
include "lemuldiv2.mm"
include "mp3an3.mm"
include "syl2anr.mm"
include "biimprd.mm"
include "impr.mm"
include "eqbrtrd.mm"
include "bldisj.mm"
include "syl33anc.mm"

theorem bl2in
  let cD: class D
  let cP: class P
  let cQ: class Q
  let cR: class R
  let cX: class X
  let cA: class A
  let vx: setvar x
  let vr: setvar r
  let vy: setvar y
  let wph: wff ph
  let cS: class S


  assert |- ( ( ( D e. ( Met ` X ) /\ P e. X /\ Q e. X ) /\ ( R e. RR /\ R <_ ( ( P D Q ) / 2 ) ) ) -> ( ( P ( ball ` D ) R ) i^i ( Q ( ball ` D ) R ) ) = (/) )

  proof
    cD
    cX
    cme
    cfv
    wcel
    #
    cP
    cX
    wcel
    #
    cQ
    cX
    wcel
    #
    w3a
    #
    cR
    cr
    wcel
    #
    cR
    cP
    cQ
    cD
    co
    #
    c2
    cdiv
    co
    cle
    wbr
    #
    wa
    #
    wa
    #
    cD
    cX
    cxmt
    cfv
    wcel
    #
    @1
    @2
    cR
    cxr
    wcel
    #
    @10
    cR
    cR
    cxad
    co
    #
    @5
    cle
    wbr
    cP
    cR
    cD
    cbl
    cfv
    #
    co
    cQ
    cR
    @12
    co
    cin
    c0
    wceq
    @8
    @0
    @9
    @0
    @1
    @2
    @7
    simpl1
    cD
    cX
    metxmet
    syl
    @0
    @1
    @2
    @7
    simpl2
    @0
    @1
    @2
    @7
    simpl3
    @4
    @10
    @3
    @6
    cR
    rexr
    ad2antrl
    #
    @13
    @8
    @11
    c2
    cR
    cmul
    co
    #
    @5
    cle
    @8
    @11
    cR
    cR
    caddc
    co
    #
    @14
    @8
    @4
    @4
    @11
    @15
    wceq
    @3
    @4
    @6
    simprl
    #
    @16
    cR
    cR
    rexadd
    syl2anc
    @8
    cR
    @8
    cR
    @16
    recnd
    2timesd
    eqtr4d
    @3
    @4
    @6
    @14
    @5
    cle
    wbr
    #
    @3
    @4
    wa
    @17
    @6
    @4
    @4
    @5
    cr
    wcel
    #
    @17
    @6
    wb
    #
    @3
    @4
    id
    cP
    cQ
    cD
    cX
    metcl
    @4
    @18
    c2
    cr
    wcel
    #
    cc0
    c2
    clt
    wbr
    #
    wa
    @19
    @20
    @21
    2re
    2pos
    pm3.2i
    cR
    @5
    c2
    lemuldiv2
    mp3an3
    syl2anr
    biimprd
    impr
    eqbrtrd
    cD
    cP
    cQ
    cR
    cR
    cX
    bldisj
    syl33anc
end
