include "cdm.mm"
include "cxp.mm"
include "wrel.mm"
include "cv.mm"
include "cpr.mm"
include "cglb.mm"
include "cfv.mm"
include "wcel.mm"
include "copab.mm"
include "relopab.mm"
include "wceq.mm"
include "eqid.mm"
include "meetdm.mm"
include "syl.mm"
include "releqd.mm"
include "mpbiri.mm"
include "cop.mm"
include "cvv.mm"
include "vex.mm"
include "a1i.mm"
include "meetdef.mm"
include "wss.mm"
include "wa.mm"
include "cple.mm"
include "adantr.mm"
include "simpr.mm"
include "glbelss.mm"
include "ex.mm"
include "prss.mm"
include "opelxpi.mm"
include "sylbir.mm"
include "syl6.mm"
include "sylbid.mm"
include "relssdv.mm"

theorem meetdmss
  let wph: wff ph
  let cB: class B
  let cK: class K
  let c.an: class ./\
  let cV: class V
  let vx: setvar x
  let vy: setvar y
  assume meetdmss.b: |- B = ( Base ` K )
  assume meetdmss.j: |- ./\ = ( meet ` K )
  assume meetdmss.k: |- ( ph -> K e. V )


  assert |- ( ph -> dom ./\ C_ ( B X. B ) )

  proof
    wph
    vx
    vy
    c.an
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
    cglb
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
    meetdmss.k
    vx
    vy
    @5
    cK
    c.an
    cV
    @5
    eqid
    #
    meetdmss.j
    meetdm
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
    cK
    c.an
    cV
    cvv
    @2
    @3
    cvv
    @9
    meetdmss.j
    meetdmss.k
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
    meetdef
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
    meetdmss.b
    @15
    eqid
    @9
    wph
    @8
    @6
    meetdmss.k
    adantr
    wph
    @6
    simpr
    glbelss
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
