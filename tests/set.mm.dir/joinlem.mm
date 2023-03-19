include "cv.mm"
include "wbr.mm"
include "wa.mm"
include "wi.mm"
include "wral.mm"
include "co.mm"
include "wsbc.mm"
include "crio.mm"
include "wreu.mm"
include "joineu.mm"
include "riotasbc.mm"
include "syl.mm"
include "joinval2.mm"
include "sbceq1d.mm"
include "mpbird.mm"
include "ovex.mm"
include "wceq.mm"
include "breq2.mm"
include "anbi12d.mm"
include "breq1.mm"
include "imbi2d.mm"
include "ralbidv.mm"
include "sbcie.mm"
include "sylib.mm"

theorem joinlem
  let wph: wff ph
  let vz: setvar z
  let cB: class B
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cV: class V
  let cX: class X
  let cY: class Y
  let vx: setvar x
  let vy: setvar y
  assume joinval2.b: |- B = ( Base ` K )
  assume joinval2.l: |- .<_ = ( le ` K )
  assume joinval2.j: |- .\/ = ( join ` K )
  assume joinval2.k: |- ( ph -> K e. V )
  assume joinval2.x: |- ( ph -> X e. B )
  assume joinval2.y: |- ( ph -> Y e. B )
  assume joinlem.e: |- ( ph -> <. X , Y >. e. dom .\/ )

  disjoint B z
  disjoint .\/ z
  disjoint K z
  disjoint X z
  disjoint Y z
  disjoint x z
  disjoint B x
  disjoint .\/ x
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
  assert |- ( ph -> ( ( X .<_ ( X .\/ Y ) /\ Y .<_ ( X .\/ Y ) ) /\ A. z e. B ( ( X .<_ z /\ Y .<_ z ) -> ( X .\/ Y ) .<_ z ) ) )

  proof
    wph
    cX
    vx
    cv
    #
    c.le
    wbr
    #
    cY
    @0
    c.le
    wbr
    #
    wa
    #
    cX
    vz
    cv
    #
    c.le
    wbr
    cY
    @4
    c.le
    wbr
    wa
    #
    @0
    @4
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
    c.or
    co
    #
    wsbc
    #
    cX
    @10
    c.le
    wbr
    #
    cY
    @10
    c.le
    wbr
    #
    wa
    #
    @5
    @10
    @4
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
    joinlem.e
    joineu
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
    joinval2
    sbceq1d
    mpbird
    @9
    @18
    vx
    @10
    cX
    cY
    c.or
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
    breq2
    @0
    @10
    cY
    c.le
    breq2
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
    breq1
    imbi2d
    ralbidv
    anbi12d
    sbcie
    sylib
end
