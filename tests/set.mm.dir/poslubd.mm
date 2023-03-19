include "cfv.mm"
include "cv.mm"
include "wbr.mm"
include "wral.mm"
include "wi.mm"
include "wa.mm"
include "crio.mm"
include "cpo.mm"
include "biid.mm"
include "lubval.mm"
include "wceq.mm"
include "ralrimiva.mm"
include "wcel.mm"
include "3expia.mm"
include "jca.mm"
include "wreu.mm"
include "wb.mm"
include "wrex.mm"
include "wrmo.mm"
include "breq2.mm"
include "ralbidv.mm"
include "breq1.mm"
include "imbi2d.mm"
include "anbi12d.mm"
include "rspcev.mm"
include "syl2anc.mm"
include "wss.mm"
include "poslubmo.mm"
include "reu5.mm"
include "sylanbrc.mm"
include "riota2.mm"
include "mpbid.mm"
include "eqtrd.mm"

theorem poslubd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cS: class S
  let cT: class T
  let cU: class U
  let cK: class K
  let c.le: class .<_
  let vz: setvar z
  assume poslubd.l: |- .<_ = ( le ` K )
  assume poslubd.b: |- B = ( Base ` K )
  assume poslubd.u: |- U = ( lub ` K )
  assume poslubd.k: |- ( ph -> K e. Poset )
  assume poslubd.s: |- ( ph -> S C_ B )
  assume poslubd.t: |- ( ph -> T e. B )
  assume poslubd.ub: |- ( ( ph /\ x e. S ) -> x .<_ T )
  assume poslubd.le: |- ( ( ph /\ y e. B /\ A. x e. S x .<_ y ) -> T .<_ y )

  disjoint .<_ x
  disjoint .<_ y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint K x
  disjoint K y
  disjoint S x
  disjoint S y
  disjoint U x
  disjoint U y
  disjoint T x
  disjoint T y
  disjoint ph x
  disjoint ph y
  disjoint .<_ z
  disjoint x z
  disjoint y z
  disjoint B z
  disjoint K z
  disjoint S z
  disjoint U z
  disjoint T z
  disjoint ph z
  assert |- ( ph -> ( U ` S ) = T )

  proof
    wph
    cS
    cU
    cfv
    vx
    cv
    #
    vz
    cv
    #
    c.le
    wbr
    #
    vx
    cS
    wral
    #
    @0
    vy
    cv
    #
    c.le
    wbr
    vx
    cS
    wral
    #
    @1
    @4
    c.le
    wbr
    #
    wi
    #
    vy
    cB
    wral
    #
    wa
    #
    vz
    cB
    crio
    #
    cT
    wph
    @9
    vz
    vx
    vy
    cB
    cS
    cU
    cK
    c.le
    cpo
    poslubd.b
    poslubd.l
    poslubd.u
    @9
    biid
    poslubd.k
    poslubd.s
    lubval
    wph
    @0
    cT
    c.le
    wbr
    #
    vx
    cS
    wral
    #
    @5
    cT
    @4
    c.le
    wbr
    #
    wi
    #
    vy
    cB
    wral
    #
    wa
    #
    @10
    cT
    wceq
    #
    wph
    @12
    @15
    wph
    @11
    vx
    cS
    poslubd.ub
    ralrimiva
    wph
    @14
    vy
    cB
    wph
    @4
    cB
    wcel
    @5
    @13
    poslubd.le
    3expia
    ralrimiva
    jca
    #
    wph
    cT
    cB
    wcel
    #
    @9
    vz
    cB
    wreu
    #
    @16
    @17
    wb
    poslubd.t
    wph
    @9
    vz
    cB
    wrex
    #
    @9
    vz
    cB
    wrmo
    #
    @20
    wph
    @19
    @16
    @21
    poslubd.t
    @18
    @9
    @16
    vz
    cT
    cB
    @1
    cT
    wceq
    #
    @3
    @12
    @8
    @15
    @23
    @2
    @11
    vx
    cS
    @1
    cT
    @0
    c.le
    breq2
    ralbidv
    @23
    @7
    @14
    vy
    cB
    @23
    @6
    @13
    @5
    @1
    cT
    @4
    c.le
    breq1
    imbi2d
    ralbidv
    anbi12d
    #
    rspcev
    syl2anc
    wph
    cK
    cpo
    wcel
    cS
    cB
    wss
    @22
    poslubd.k
    poslubd.s
    vz
    vx
    vy
    cB
    cS
    cK
    c.le
    poslubd.l
    poslubd.b
    poslubmo
    syl2anc
    @9
    vz
    cB
    reu5
    sylanbrc
    @9
    @16
    vz
    cB
    cT
    @24
    riota2
    syl2anc
    mpbid
    eqtrd
end
