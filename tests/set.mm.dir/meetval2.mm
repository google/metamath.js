include "co.mm"
include "cpr.mm"
include "cglb.mm"
include "cfv.mm"
include "cv.mm"
include "wbr.mm"
include "wral.mm"
include "wi.mm"
include "wa.mm"
include "crio.mm"
include "eqid.mm"
include "meetval.mm"
include "biid.mm"
include "wcel.mm"
include "wss.mm"
include "prssi.mm"
include "syl2anc.mm"
include "glbval.mm"
include "wceq.mm"
include "meetval2lem.mm"
include "riotabidv.mm"
include "3eqtrd.mm"

theorem meetval2
  let wph: wff ph
  let vx: setvar x
  let vz: setvar z
  let cB: class B
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cV: class V
  let cX: class X
  let cY: class Y
  let vy: setvar y
  assume meetval2.b: |- B = ( Base ` K )
  assume meetval2.l: |- .<_ = ( le ` K )
  assume meetval2.m: |- ./\ = ( meet ` K )
  assume meetval2.k: |- ( ph -> K e. V )
  assume meetval2.x: |- ( ph -> X e. B )
  assume meetval2.y: |- ( ph -> Y e. B )

  disjoint x z
  disjoint B x
  disjoint B z
  disjoint ./\ x
  disjoint ./\ z
  disjoint K x
  disjoint K z
  disjoint X x
  disjoint X z
  disjoint Y x
  disjoint Y z
  disjoint x y
  disjoint y z
  disjoint K y
  disjoint .<_ y
  disjoint X y
  disjoint Y y
  assert |- ( ph -> ( X ./\ Y ) = ( iota_ x e. B ( ( x .<_ X /\ x .<_ Y ) /\ A. z e. B ( ( z .<_ X /\ z .<_ Y ) -> z .<_ x ) ) ) )

  proof
    wph
    cX
    cY
    c.an
    co
    cX
    cY
    cpr
    #
    cK
    cglb
    cfv
    #
    cfv
    vx
    cv
    #
    vy
    cv
    #
    c.le
    wbr
    vy
    @0
    wral
    vz
    cv
    #
    @3
    c.le
    wbr
    vy
    @0
    wral
    @4
    @2
    c.le
    wbr
    #
    wi
    vz
    cB
    wral
    wa
    #
    vx
    cB
    crio
    #
    @2
    cX
    c.le
    wbr
    @2
    cY
    c.le
    wbr
    wa
    @4
    cX
    c.le
    wbr
    @4
    cY
    c.le
    wbr
    wa
    @5
    wi
    vz
    cB
    wral
    wa
    #
    vx
    cB
    crio
    #
    wph
    @1
    cK
    c.an
    cV
    cB
    cX
    cY
    cB
    @1
    eqid
    #
    meetval2.m
    meetval2.k
    meetval2.x
    meetval2.y
    meetval
    wph
    @6
    vx
    vy
    vz
    cB
    @0
    @1
    cK
    c.le
    cV
    meetval2.b
    meetval2.l
    @10
    @6
    biid
    meetval2.k
    wph
    cX
    cB
    wcel
    #
    cY
    cB
    wcel
    #
    @0
    cB
    wss
    meetval2.x
    meetval2.y
    cX
    cY
    cB
    prssi
    syl2anc
    glbval
    wph
    @11
    @12
    @7
    @9
    wceq
    meetval2.x
    meetval2.y
    @11
    @12
    wa
    @6
    @8
    vx
    cB
    wph
    vx
    vy
    vz
    cB
    cK
    c.le
    c.an
    cV
    cX
    cY
    meetval2.b
    meetval2.l
    meetval2.m
    meetval2.k
    meetval2.x
    meetval2.y
    meetval2lem
    riotabidv
    syl2anc
    3eqtrd
end
