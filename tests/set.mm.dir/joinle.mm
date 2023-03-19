include "wbr.mm"
include "wa.mm"
include "co.mm"
include "wcel.mm"
include "cv.mm"
include "wi.mm"
include "wral.mm"
include "cpo.mm"
include "joinlem.mm"
include "simprd.mm"
include "wceq.mm"
include "breq2.mm"
include "anbi12d.mm"
include "imbi12d.mm"
include "rspcva.mm"
include "syl2anc.mm"
include "lejoin1.mm"
include "joincl.mm"
include "postr.mm"
include "syl13anc.mm"
include "mpand.mm"
include "lejoin2.mm"
include "jcad.mm"
include "impbid.mm"

theorem joinle
  let wph: wff ph
  let cB: class B
  let c.or: class .\/
  let cK: class K
  let c.le: class .<_
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vz: setvar z
  assume joinle.b: |- B = ( Base ` K )
  assume joinle.l: |- .<_ = ( le ` K )
  assume joinle.j: |- .\/ = ( join ` K )
  assume joinle.k: |- ( ph -> K e. Poset )
  assume joinle.x: |- ( ph -> X e. B )
  assume joinle.y: |- ( ph -> Y e. B )
  assume joinle.z: |- ( ph -> Z e. B )
  assume joinle.e: |- ( ph -> <. X , Y >. e. dom .\/ )


  assert |- ( ph -> ( ( X .<_ Z /\ Y .<_ Z ) <-> ( X .\/ Y ) .<_ Z ) )

  proof
    wph
    cX
    cZ
    c.le
    wbr
    #
    cY
    cZ
    c.le
    wbr
    #
    wa
    #
    cX
    cY
    c.or
    co
    #
    cZ
    c.le
    wbr
    #
    wph
    cZ
    cB
    wcel
    #
    cX
    vz
    cv
    #
    c.le
    wbr
    #
    cY
    @6
    c.le
    wbr
    #
    wa
    #
    @3
    @6
    c.le
    wbr
    #
    wi
    #
    vz
    cB
    wral
    #
    @2
    @4
    wi
    #
    joinle.z
    wph
    cX
    @3
    c.le
    wbr
    #
    cY
    @3
    c.le
    wbr
    #
    wa
    @12
    wph
    vz
    cB
    c.or
    cK
    c.le
    cpo
    cX
    cY
    joinle.b
    joinle.l
    joinle.j
    joinle.k
    joinle.x
    joinle.y
    joinle.e
    joinlem
    simprd
    @11
    @13
    vz
    cZ
    cB
    @6
    cZ
    wceq
    #
    @9
    @2
    @10
    @4
    @16
    @7
    @0
    @8
    @1
    @6
    cZ
    cX
    c.le
    breq2
    @6
    cZ
    cY
    c.le
    breq2
    anbi12d
    @6
    cZ
    @3
    c.le
    breq2
    imbi12d
    rspcva
    syl2anc
    wph
    @4
    @0
    @1
    wph
    @14
    @4
    @0
    wph
    cB
    c.or
    cK
    c.le
    cpo
    cX
    cY
    joinle.b
    joinle.l
    joinle.j
    joinle.k
    joinle.x
    joinle.y
    joinle.e
    lejoin1
    wph
    cK
    cpo
    wcel
    #
    cX
    cB
    wcel
    @3
    cB
    wcel
    #
    @5
    @14
    @4
    wa
    @0
    wi
    joinle.k
    joinle.x
    wph
    cB
    c.or
    cK
    cpo
    cX
    cY
    joinle.b
    joinle.j
    joinle.k
    joinle.x
    joinle.y
    joinle.e
    joincl
    #
    joinle.z
    cB
    cK
    c.le
    cX
    @3
    cZ
    joinle.b
    joinle.l
    postr
    syl13anc
    mpand
    wph
    @15
    @4
    @1
    wph
    cB
    c.or
    cK
    c.le
    cpo
    cX
    cY
    joinle.b
    joinle.l
    joinle.j
    joinle.k
    joinle.x
    joinle.y
    joinle.e
    lejoin2
    wph
    @17
    cY
    cB
    wcel
    @18
    @5
    @15
    @4
    wa
    @1
    wi
    joinle.k
    joinle.y
    @19
    joinle.z
    cB
    cK
    c.le
    cY
    @3
    cZ
    joinle.b
    joinle.l
    postr
    syl13anc
    mpand
    jcad
    impbid
end
