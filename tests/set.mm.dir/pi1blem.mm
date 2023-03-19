include "cphtpc.mm"
include "cfv.mm"
include "cima.mm"
include "wss.mm"
include "cii.mm"
include "ccn.mm"
include "co.mm"
include "cv.mm"
include "wcel.mm"
include "wbr.mm"
include "wrex.mm"
include "vex.mm"
include "elima.mm"
include "wa.mm"
include "cc0.mm"
include "wceq.mm"
include "c1.mm"
include "cphtpy.mm"
include "c0.mm"
include "wne.mm"
include "w3a.mm"
include "simpr.mm"
include "isphtpc.mm"
include "sylib.mm"
include "adantrl.mm"
include "simp2d.mm"
include "phtpc01.mm"
include "ad2antll.mm"
include "simpld.mm"
include "om1elbas.mm"
include "biimpa.mm"
include "adantrr.mm"
include "eqtr3d.mm"
include "simprd.mm"
include "simp3d.mm"
include "wb.mm"
include "adantr.mm"
include "mpbir3and.mm"
include "rexlimdvaa.mm"
include "syl5bi.mm"
include "ssrdv.mm"
include "simp1.mm"
include "syl6bi.mm"
include "jca.mm"

theorem pi1blem
  let wph: wff ph
  let cB: class B
  let cG: class G
  let cJ: class J
  let cK: class K
  let cO: class O
  let cX: class X
  let cY: class Y
  let vj: setvar j
  let vx: setvar x
  let vy: setvar y
  assume pi1val.g: |- G = ( J pi1 Y )
  assume pi1val.1: |- ( ph -> J e. ( TopOn ` X ) )
  assume pi1val.2: |- ( ph -> Y e. X )
  assume pi1val.o: |- O = ( J Om1 Y )
  assume pi1bas.b: |- ( ph -> B = ( Base ` G ) )
  assume pi1bas.k: |- ( ph -> K = ( Base ` O ) )


  assert |- ( ph -> ( ( ( ~=ph ` J ) " K ) C_ K /\ K C_ ( II Cn J ) ) )

  proof
    wph
    cJ
    cphtpc
    cfv
    #
    cK
    cima
    #
    cK
    wss
    cK
    cii
    cJ
    ccn
    co
    #
    wss
    wph
    vx
    @1
    cK
    vx
    cv
    #
    @1
    wcel
    vy
    cv
    #
    @3
    @0
    wbr
    #
    vy
    cK
    wrex
    wph
    @3
    cK
    wcel
    #
    vy
    @3
    @0
    cK
    vx
    vex
    elima
    wph
    @5
    @6
    vy
    cK
    wph
    @4
    cK
    wcel
    #
    @5
    wa
    #
    wa
    #
    @6
    @3
    @2
    wcel
    #
    cc0
    @3
    cfv
    #
    cY
    wceq
    #
    c1
    @3
    cfv
    #
    cY
    wceq
    #
    @9
    @4
    @2
    wcel
    #
    @10
    @4
    @3
    cJ
    cphtpy
    cfv
    co
    c0
    wne
    #
    wph
    @5
    @15
    @10
    @16
    w3a
    #
    @7
    wph
    @5
    wa
    @5
    @17
    wph
    @5
    simpr
    @4
    @3
    cJ
    isphtpc
    sylib
    adantrl
    simp2d
    @9
    cc0
    @4
    cfv
    #
    @11
    cY
    @9
    @18
    @11
    wceq
    #
    c1
    @4
    cfv
    #
    @13
    wceq
    #
    @5
    @19
    @21
    wa
    wph
    @7
    @4
    @3
    cJ
    phtpc01
    ad2antll
    #
    simpld
    @9
    @15
    @18
    cY
    wceq
    #
    @20
    cY
    wceq
    #
    wph
    @7
    @15
    @23
    @24
    w3a
    #
    @5
    wph
    @7
    @25
    wph
    cK
    @4
    cJ
    cO
    cX
    cY
    pi1val.o
    pi1val.1
    pi1val.2
    pi1bas.k
    om1elbas
    biimpa
    adantrr
    #
    simp2d
    eqtr3d
    @9
    @20
    @13
    cY
    @9
    @19
    @21
    @22
    simprd
    @9
    @15
    @23
    @24
    @26
    simp3d
    eqtr3d
    wph
    @6
    @10
    @12
    @14
    w3a
    #
    wb
    @8
    wph
    cK
    @3
    cJ
    cO
    cX
    cY
    pi1val.o
    pi1val.1
    pi1val.2
    pi1bas.k
    om1elbas
    #
    adantr
    mpbir3and
    rexlimdvaa
    syl5bi
    ssrdv
    wph
    vx
    cK
    @2
    wph
    @6
    @27
    @10
    @28
    @10
    @12
    @14
    simp1
    syl6bi
    ssrdv
    jca
end
