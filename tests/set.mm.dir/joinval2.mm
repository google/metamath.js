include "co.mm"
include "cpr.mm"
include "club.mm"
include "cfv.mm"
include "cv.mm"
include "wbr.mm"
include "wral.mm"
include "wi.mm"
include "wa.mm"
include "crio.mm"
include "eqid.mm"
include "joinval.mm"
include "biid.mm"
include "wcel.mm"
include "wss.mm"
include "prssi.mm"
include "syl2anc.mm"
include "lubval.mm"
include "wceq.mm"
include "joinval2lem.mm"
include "riotabidv.mm"
include "3eqtrd.mm"

theorem joinval2
  let wph: wff ph
  let vx: setvar x
  let vz: setvar z
  let cB: class B
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cV: class V
  let cX: class X
  let cY: class Y
  let vy: setvar y
  assume joinval2.b: |- B = ( Base ` K )
  assume joinval2.l: |- .<_ = ( le ` K )
  assume joinval2.j: |- .\/ = ( join ` K )
  assume joinval2.k: |- ( ph -> K e. V )
  assume joinval2.x: |- ( ph -> X e. B )
  assume joinval2.y: |- ( ph -> Y e. B )

  disjoint x z
  disjoint B x
  disjoint B z
  disjoint .\/ x
  disjoint .\/ z
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
  assert |- ( ph -> ( X .\/ Y ) = ( iota_ x e. B ( ( X .<_ x /\ Y .<_ x ) /\ A. z e. B ( ( X .<_ z /\ Y .<_ z ) -> x .<_ z ) ) ) )

  proof
    wph
    cX
    cY
    c.or
    co
    cX
    cY
    cpr
    #
    cK
    club
    cfv
    #
    cfv
    vy
    cv
    #
    vx
    cv
    #
    c.le
    wbr
    vy
    @0
    wral
    @2
    vz
    cv
    #
    c.le
    wbr
    vy
    @0
    wral
    @3
    @4
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
    cX
    @3
    c.le
    wbr
    cY
    @3
    c.le
    wbr
    wa
    cX
    @4
    c.le
    wbr
    cY
    @4
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
    c.or
    cK
    cV
    cB
    cX
    cY
    cB
    @1
    eqid
    #
    joinval2.j
    joinval2.k
    joinval2.x
    joinval2.y
    joinval
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
    joinval2.b
    joinval2.l
    @10
    @6
    biid
    joinval2.k
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
    joinval2.x
    joinval2.y
    cX
    cY
    cB
    prssi
    syl2anc
    lubval
    wph
    @11
    @12
    @7
    @9
    wceq
    joinval2.x
    joinval2.y
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
    c.or
    cK
    c.le
    cV
    cX
    cY
    joinval2.b
    joinval2.l
    joinval2.j
    joinval2.k
    joinval2.x
    joinval2.y
    joinval2lem
    riotabidv
    syl2anc
    3eqtrd
end
