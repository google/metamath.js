include "cop.mm"
include "cdm.mm"
include "wcel.mm"
include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "wi.mm"
include "wral.mm"
include "wreu.mm"
include "cpr.mm"
include "club.mm"
include "cfv.mm"
include "eqid.mm"
include "joindef.mm"
include "biid.mm"
include "adantr.mm"
include "simpr.mm"
include "lubeu.mm"
include "ex.mm"
include "wb.mm"
include "joinval2lem.mm"
include "syl2anc.mm"
include "reubidv.mm"
include "sylibd.mm"
include "sylbid.mm"
include "mpd.mm"

theorem joineu
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
  assume joinlem.e: |- ( ph -> <. X , Y >. e. dom .\/ )

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
  disjoint ph x
  disjoint x y
  disjoint y z
  disjoint K y
  disjoint .<_ y
  disjoint X y
  disjoint Y y
  assert |- ( ph -> E! x e. B ( ( X .<_ x /\ Y .<_ x ) /\ A. z e. B ( ( X .<_ z /\ Y .<_ z ) -> x .<_ z ) ) )

  proof
    wph
    cX
    cY
    cop
    c.or
    cdm
    wcel
    #
    cX
    vx
    cv
    #
    c.le
    wbr
    cY
    @1
    c.le
    wbr
    wa
    cX
    vz
    cv
    #
    c.le
    wbr
    cY
    @2
    c.le
    wbr
    wa
    @1
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
    wreu
    #
    joinlem.e
    wph
    @0
    cX
    cY
    cpr
    #
    cK
    club
    cfv
    #
    cdm
    wcel
    #
    @5
    wph
    @7
    c.or
    cK
    cV
    cB
    cX
    cY
    cB
    @7
    eqid
    #
    joinval2.j
    joinval2.k
    joinval2.x
    joinval2.y
    joindef
    wph
    @8
    vy
    cv
    #
    @1
    c.le
    wbr
    vy
    @6
    wral
    @10
    @2
    c.le
    wbr
    vy
    @6
    wral
    @3
    wi
    vz
    cB
    wral
    wa
    #
    vx
    cB
    wreu
    #
    @5
    wph
    @8
    @12
    wph
    @8
    wa
    @11
    vx
    vy
    vz
    cB
    @6
    @7
    cK
    c.le
    cV
    joinval2.b
    joinval2.l
    @9
    @11
    biid
    wph
    cK
    cV
    wcel
    @8
    joinval2.k
    adantr
    wph
    @8
    simpr
    lubeu
    ex
    wph
    @11
    @4
    vx
    cB
    wph
    cX
    cB
    wcel
    cY
    cB
    wcel
    @11
    @4
    wb
    joinval2.x
    joinval2.y
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
    syl2anc
    reubidv
    sylibd
    sylbid
    mpd
end
