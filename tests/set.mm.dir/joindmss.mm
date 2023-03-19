include "cdm.mm"
include "cxp.mm"
include "wrel.mm"
include "cv.mm"
include "cpr.mm"
include "club.mm"
include "cfv.mm"
include "wcel.mm"
include "copab.mm"
include "relopab.mm"
include "wceq.mm"
include "eqid.mm"
include "joindm.mm"
include "syl.mm"
include "releqd.mm"
include "mpbiri.mm"
include "cop.mm"
include "cvv.mm"
include "vex.mm"
include "a1i.mm"
include "joindef.mm"
include "wss.mm"
include "wa.mm"
include "cple.mm"
include "adantr.mm"
include "simpr.mm"
include "lubelss.mm"
include "ex.mm"
include "prss.mm"
include "opelxpi.mm"
include "sylbir.mm"
include "syl6.mm"
include "sylbid.mm"
include "relssdv.mm"

theorem joindmss
  let wph: wff ph
  let cB: class B
  let c.or: class .\/
  let cK: class K
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  assume joindmss.b: |- B = ( Base ` K )
  assume joindmss.j: |- .\/ = ( join ` K )
  assume joindmss.k: |- ( ph -> K e. V )


  assert |- ( ph -> dom .\/ C_ ( B X. B ) )

  proof
    wph
    vx
    vy
    c.or
    cdm
    #
    cB
    cB
    cxp
    #
    wph
    @0
    wrel
    vx
    cv
    #
    vy
    cv
    #
    cpr
    #
    cK
    club
    cfv
    #
    cdm
    wcel
    #
    vx
    vy
    copab
    #
    wrel
    @6
    vx
    vy
    relopab
    wph
    @0
    @7
    wph
    cK
    cV
    wcel
    #
    @0
    @7
    wceq
    joindmss.k
    vx
    vy
    @5
    c.or
    cK
    cV
    @5
    eqid
    #
    joindmss.j
    joindm
    syl
    releqd
    mpbiri
    wph
    @2
    @3
    cop
    #
    @0
    wcel
    @6
    @10
    @1
    wcel
    #
    wph
    @5
    c.or
    cK
    cV
    cvv
    @2
    @3
    cvv
    @9
    joindmss.j
    joindmss.k
    @2
    cvv
    wcel
    wph
    vx
    vex
    #
    a1i
    @3
    cvv
    wcel
    wph
    vy
    vex
    #
    a1i
    joindef
    wph
    @6
    @4
    cB
    wss
    #
    @11
    wph
    @6
    @14
    wph
    @6
    wa
    cB
    @4
    @5
    cK
    cK
    cple
    cfv
    #
    cV
    joindmss.b
    @15
    eqid
    @9
    wph
    @8
    @6
    joindmss.k
    adantr
    wph
    @6
    simpr
    lubelss
    ex
    @14
    @2
    cB
    wcel
    @3
    cB
    wcel
    wa
    @11
    @2
    @3
    cB
    @12
    @13
    prss
    @2
    @3
    cB
    cB
    opelxpi
    sylbir
    syl6
    sylbid
    relssdv
end
