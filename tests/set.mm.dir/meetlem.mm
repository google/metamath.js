include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "wi.mm"
include "wral.mm"
include "co.mm"
include "wsbc.mm"
include "crio.mm"
include "wreu.mm"
include "meeteu.mm"
include "riotasbc.mm"
include "syl.mm"
include "meetval2.mm"
include "sbceq1d.mm"
include "mpbird.mm"
include "ovex.mm"
include "wceq.mm"
include "breq1.mm"
include "anbi12d.mm"
include "breq2.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "sbcie.mm"
include "sylib.mm"

theorem meetlem
  let wph: wff ph
  let vz: setvar z
  let cB: class B
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cV: class V
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  assume meetval2.b: |- B = ( Base ` K )
  assume meetval2.l: |- .<_ = ( le ` K )
  assume meetval2.m: |- ./\ = ( meet ` K )
  assume meetval2.k: |- ( ph -> K e. V )
  assume meetval2.x: |- ( ph -> X e. B )
  assume meetval2.y: |- ( ph -> Y e. B )
  assume meetlem.e: |- ( ph -> <. X , Y >. e. dom ./\ )

  disjoint B z
  disjoint ./\ z
  disjoint K z
  disjoint X z
  disjoint Y z
  disjoint x z
  disjoint B x
  disjoint ./\ x
  disjoint x y
  disjoint K x
  disjoint y z
  disjoint K y
  disjoint .<_ y
  disjoint X x
  disjoint X y
  disjoint Y x
  disjoint Y y
  disjoint ph x
  disjoint .<_ x
  assert |- ( ph -> ( ( ( X ./\ Y ) .<_ X /\ ( X ./\ Y ) .<_ Y ) /\ A. z e. B ( ( z .<_ X /\ z .<_ Y ) -> z .<_ ( X ./\ Y ) ) ) )

  proof
    wph
    vx
    cv
    #
    cX
    c.le
    wbr
    #
    @0
    cY
    c.le
    wbr
    #
    wa
    #
    vz
    cv
    #
    cX
    c.le
    wbr
    @4
    cY
    c.le
    wbr
    wa
    #
    @4
    @0
    c.le
    wbr
    #
    wi
    #
    vz
    cB
    wral
    #
    wa
    #
    vx
    cX
    cY
    c.an
    co
    #
    wsbc
    #
    @10
    cX
    c.le
    wbr
    #
    @10
    cY
    c.le
    wbr
    #
    wa
    #
    @5
    @4
    @10
    c.le
    wbr
    #
    wi
    #
    vz
    cB
    wral
    #
    wa
    #
    wph
    @11
    @9
    vx
    @9
    vx
    cB
    crio
    #
    wsbc
    #
    wph
    @9
    vx
    cB
    wreu
    @20
    wph
    vx
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
    meetlem.e
    meeteu
    @9
    vx
    cB
    riotasbc
    syl
    wph
    @9
    vx
    @10
    @19
    wph
    vx
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
    meetval2
    sbceq1d
    mpbird
    @9
    @18
    vx
    @10
    cX
    cY
    c.an
    ovex
    @0
    @10
    wceq
    #
    @3
    @14
    @8
    @17
    @21
    @1
    @12
    @2
    @13
    @0
    @10
    cX
    c.le
    breq1
    @0
    @10
    cY
    c.le
    breq1
    anbi12d
    @21
    @7
    @16
    vz
    cB
    @21
    @6
    @15
    @5
    @0
    @10
    @4
    c.le
    breq2
    imbi2d
    ralbidv
    anbi12d
    sbcie
    sylib
end
