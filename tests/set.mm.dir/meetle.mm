include "wbr.mm"
include "wa.mm"
include "co.mm"
include "wcel.mm"
include "cv.mm"
include "wi.mm"
include "wral.mm"
include "cpo.mm"
include "meetlem.mm"
include "simprd.mm"
include "wceq.mm"
include "breq1.mm"
include "anbi12d.mm"
include "imbi12d.mm"
include "rspcva.mm"
include "syl2anc.mm"
include "lemeet1.mm"
include "meetcl.mm"
include "postr.mm"
include "syl13anc.mm"
include "mpan2d.mm"
include "lemeet2.mm"
include "jcad.mm"
include "impbid.mm"

theorem meetle
  let wph: wff ph
  let cB: class B
  let cK: class K
  let c.le: class .<_
  let c.an: class ./\
  let cX: class X
  let cY: class Y
  let cZ: class Z
  let vz: setvar z
  assume meetle.b: |- B = ( Base ` K )
  assume meetle.l: |- .<_ = ( le ` K )
  assume meetle.m: |- ./\ = ( meet ` K )
  assume meetle.k: |- ( ph -> K e. Poset )
  assume meetle.x: |- ( ph -> X e. B )
  assume meetle.y: |- ( ph -> Y e. B )
  assume meetle.z: |- ( ph -> Z e. B )
  assume meetle.e: |- ( ph -> <. X , Y >. e. dom ./\ )


  assert |- ( ph -> ( ( Z .<_ X /\ Z .<_ Y ) <-> Z .<_ ( X ./\ Y ) ) )

  proof
    wph
    cZ
    cX
    c.le
    wbr
    #
    cZ
    cY
    c.le
    wbr
    #
    wa
    #
    cZ
    cX
    cY
    c.an
    co
    #
    c.le
    wbr
    #
    wph
    cZ
    cB
    wcel
    #
    vz
    cv
    #
    cX
    c.le
    wbr
    #
    @6
    cY
    c.le
    wbr
    #
    wa
    #
    @6
    @3
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
    meetle.z
    wph
    @3
    cX
    c.le
    wbr
    #
    @3
    cY
    c.le
    wbr
    #
    wa
    @12
    wph
    vz
    cB
    cK
    c.le
    c.an
    cpo
    cX
    cY
    meetle.b
    meetle.l
    meetle.m
    meetle.k
    meetle.x
    meetle.y
    meetle.e
    meetlem
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
    breq1
    @6
    cZ
    cY
    c.le
    breq1
    anbi12d
    @6
    cZ
    @3
    c.le
    breq1
    imbi12d
    rspcva
    syl2anc
    wph
    @4
    @0
    @1
    wph
    @4
    @14
    @0
    wph
    cB
    cK
    c.le
    c.an
    cpo
    cX
    cY
    meetle.b
    meetle.l
    meetle.m
    meetle.k
    meetle.x
    meetle.y
    meetle.e
    lemeet1
    wph
    cK
    cpo
    wcel
    #
    @5
    @3
    cB
    wcel
    #
    cX
    cB
    wcel
    @4
    @14
    wa
    @0
    wi
    meetle.k
    meetle.z
    wph
    cB
    cK
    c.an
    cpo
    cX
    cY
    meetle.b
    meetle.m
    meetle.k
    meetle.x
    meetle.y
    meetle.e
    meetcl
    #
    meetle.x
    cB
    cK
    c.le
    cZ
    @3
    cX
    meetle.b
    meetle.l
    postr
    syl13anc
    mpan2d
    wph
    @4
    @15
    @1
    wph
    cB
    cK
    c.le
    c.an
    cpo
    cX
    cY
    meetle.b
    meetle.l
    meetle.m
    meetle.k
    meetle.x
    meetle.y
    meetle.e
    lemeet2
    wph
    @17
    @5
    @18
    cY
    cB
    wcel
    @4
    @15
    wa
    @1
    wi
    meetle.k
    meetle.z
    @19
    meetle.y
    cB
    cK
    c.le
    cZ
    @3
    cY
    meetle.b
    meetle.l
    postr
    syl13anc
    mpan2d
    jcad
    impbid
end
