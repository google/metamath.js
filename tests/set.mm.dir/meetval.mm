include "cpr.mm"
include "cdm.mm"
include "wcel.mm"
include "co.mm"
include "cfv.mm"
include "wceq.mm"
include "wa.mm"
include "cv.mm"
include "coprab.mm"
include "meetfval2.mm"
include "syl.mm"
include "oveqd.mm"
include "adantr.mm"
include "simpr.mm"
include "eqidd.mm"
include "wi.mm"
include "cvv.mm"
include "fvexd.mm"
include "w3a.mm"
include "wb.mm"
include "preq12.mm"
include "eleq1d.mm"
include "3adant3.mm"
include "simp3.mm"
include "fveq2d.mm"
include "eqeq12d.mm"
include "anbi12d.mm"
include "moeq.mm"
include "moani.mm"
include "eqid.mm"
include "ovigg.mm"
include "syl3anc.mm"
include "mp2and.mm"
include "eqtrd.mm"
include "wn.mm"
include "c0.mm"
include "cop.mm"
include "meetdef.mm"
include "notbid.mm"
include "df-ov.mm"
include "ndmfv.mm"
include "syl5eq.mm"
include "syl6bir.mm"
include "imp.mm"
include "adantl.mm"
include "eqtr4d.mm"
include "pm2.61dan.mm"

theorem meetval
  let wph: wff ph
  let cG: class G
  let cK: class K
  let c.an: class ./\
  let cV: class V
  let cW: class W
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume meetdef.u: |- G = ( glb ` K )
  assume meetdef.m: |- ./\ = ( meet ` K )
  assume meetdef.k: |- ( ph -> K e. V )
  assume meetdef.x: |- ( ph -> X e. W )
  assume meetdef.y: |- ( ph -> Y e. Z )


  assert |- ( ph -> ( X ./\ Y ) = ( G ` { X , Y } ) )

  proof
    wph
    cX
    cY
    cpr
    #
    cG
    cdm
    #
    wcel
    #
    cX
    cY
    c.an
    co
    #
    @0
    cG
    cfv
    #
    wceq
    wph
    @2
    wa
    #
    @3
    cX
    cY
    vx
    cv
    #
    vy
    cv
    #
    cpr
    #
    @1
    wcel
    #
    vz
    cv
    #
    @8
    cG
    cfv
    #
    wceq
    #
    wa
    #
    vx
    vy
    vz
    coprab
    #
    co
    #
    @4
    wph
    @3
    @15
    wceq
    @2
    wph
    c.an
    @14
    cX
    cY
    wph
    cK
    cV
    wcel
    c.an
    @14
    wceq
    meetdef.k
    vx
    vy
    vz
    cG
    cK
    c.an
    cV
    meetdef.u
    meetdef.m
    meetfval2
    syl
    oveqd
    adantr
    @5
    @2
    @4
    @4
    wceq
    #
    @15
    @4
    wceq
    #
    wph
    @2
    simpr
    @5
    @4
    eqidd
    wph
    @2
    @16
    wa
    #
    @17
    wi
    #
    @2
    wph
    cX
    cW
    wcel
    cY
    cZ
    wcel
    @4
    cvv
    wcel
    @19
    meetdef.x
    meetdef.y
    wph
    @0
    cG
    fvexd
    @13
    @18
    vx
    vy
    vz
    cX
    cY
    @4
    @14
    cW
    cZ
    cvv
    @6
    cX
    wceq
    #
    @7
    cY
    wceq
    #
    @10
    @4
    wceq
    #
    w3a
    #
    @9
    @2
    @12
    @16
    @20
    @21
    @9
    @2
    wb
    @22
    @20
    @21
    wa
    #
    @8
    @0
    @1
    @6
    @7
    cX
    cY
    preq12
    #
    eleq1d
    3adant3
    @23
    @10
    @4
    @11
    @4
    @20
    @21
    @22
    simp3
    @20
    @21
    @11
    @4
    wceq
    @22
    @24
    @8
    @0
    cG
    @25
    fveq2d
    3adant3
    eqeq12d
    anbi12d
    @12
    @9
    vz
    vz
    @11
    moeq
    moani
    @14
    eqid
    ovigg
    syl3anc
    adantr
    mp2and
    eqtrd
    wph
    @2
    wn
    #
    wa
    @3
    c0
    @4
    wph
    @26
    @3
    c0
    wceq
    #
    wph
    @26
    cX
    cY
    cop
    #
    c.an
    cdm
    wcel
    #
    wn
    #
    @27
    wph
    @29
    @2
    wph
    cG
    cK
    c.an
    cV
    cW
    cX
    cY
    cZ
    meetdef.u
    meetdef.m
    meetdef.k
    meetdef.x
    meetdef.y
    meetdef
    notbid
    @30
    @3
    @28
    c.an
    cfv
    c0
    cX
    cY
    c.an
    df-ov
    @28
    c.an
    ndmfv
    syl5eq
    syl6bir
    imp
    @26
    @4
    c0
    wceq
    wph
    @0
    cG
    ndmfv
    adantl
    eqtr4d
    pm2.61dan
end
