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
include "cglb.mm"
include "cfv.mm"
include "eqid.mm"
include "meetdef.mm"
include "biid.mm"
include "adantr.mm"
include "simpr.mm"
include "glbeu.mm"
include "ex.mm"
include "wb.mm"
include "meetval2lem.mm"
include "syl2anc.mm"
include "reubidv.mm"
include "sylibd.mm"
include "sylbid.mm"
include "mpd.mm"

theorem meeteu
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
  assume meetlem.e: |- ( ph -> <. X , Y >. e. dom ./\ )

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
  disjoint ph x
  disjoint x y
  disjoint y z
  disjoint K y
  disjoint .<_ y
  disjoint X y
  disjoint Y y
  assert |- ( ph -> E! x e. B ( ( x .<_ X /\ x .<_ Y ) /\ A. z e. B ( ( z .<_ X /\ z .<_ Y ) -> z .<_ x ) ) )

  proof
    wph
    cX
    cY
    cop
    c.an
    cdm
    wcel
    #
    vx
    cv
    #
    cX
    c.le
    wbr
    @1
    cY
    c.le
    wbr
    wa
    vz
    cv
    #
    cX
    c.le
    wbr
    @2
    cY
    c.le
    wbr
    wa
    @2
    @1
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
    meetlem.e
    wph
    @0
    cX
    cY
    cpr
    #
    cK
    cglb
    cfv
    #
    cdm
    wcel
    #
    @5
    wph
    @7
    cK
    c.an
    cV
    cB
    cX
    cY
    cB
    @7
    eqid
    #
    meetval2.m
    meetval2.k
    meetval2.x
    meetval2.y
    meetdef
    wph
    @8
    @1
    vy
    cv
    #
    c.le
    wbr
    vy
    @6
    wral
    @2
    @10
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
    meetval2.b
    meetval2.l
    @9
    @11
    biid
    wph
    cK
    cV
    wcel
    @8
    meetval2.k
    adantr
    wph
    @8
    simpr
    glbeu
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
    meetval2.x
    meetval2.y
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
    syl2anc
    reubidv
    sylibd
    sylbid
    mpd
end
