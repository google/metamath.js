include "cfv.mm"
include "club.mm"
include "fveq1d.mm"
include "cbs.mm"
include "eqid.mm"
include "sseqtrd.mm"
include "eleqtrd.mm"
include "cv.mm"
include "wcel.mm"
include "wbr.mm"
include "wral.mm"
include "eleq2d.mm"
include "biimpar.mm"
include "3adant3.mm"
include "syld3an2.mm"
include "poslubd.mm"
include "eqtrd.mm"

theorem poslubdg
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cS: class S
  let cT: class T
  let cU: class U
  let cK: class K
  let c.le: class .<_
  assume poslubdg.l: |- .<_ = ( le ` K )
  assume poslubdg.b: |- ( ph -> B = ( Base ` K ) )
  assume poslubdg.u: |- ( ph -> U = ( lub ` K ) )
  assume poslubdg.k: |- ( ph -> K e. Poset )
  assume poslubdg.s: |- ( ph -> S C_ B )
  assume poslubdg.t: |- ( ph -> T e. B )
  assume poslubdg.ub: |- ( ( ph /\ x e. S ) -> x .<_ T )
  assume poslubdg.le: |- ( ( ph /\ y e. B /\ A. x e. S x .<_ y ) -> T .<_ y )

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
  assert |- ( ph -> ( U ` S ) = T )

  proof
    wph
    cS
    cU
    cfv
    cS
    cK
    club
    cfv
    #
    cfv
    cT
    wph
    cS
    cU
    @0
    poslubdg.u
    fveq1d
    wph
    vx
    vy
    cK
    cbs
    cfv
    #
    cS
    cT
    @0
    cK
    c.le
    poslubdg.l
    @1
    eqid
    @0
    eqid
    poslubdg.k
    wph
    cS
    cB
    @1
    poslubdg.s
    poslubdg.b
    sseqtrd
    wph
    cT
    cB
    @1
    poslubdg.t
    poslubdg.b
    eleqtrd
    poslubdg.ub
    wph
    vy
    cv
    #
    cB
    wcel
    #
    @2
    @1
    wcel
    #
    vx
    cv
    @2
    c.le
    wbr
    vx
    cS
    wral
    #
    cT
    @2
    c.le
    wbr
    wph
    @4
    @3
    @5
    wph
    @3
    @4
    wph
    cB
    @1
    @2
    poslubdg.b
    eleq2d
    biimpar
    3adant3
    poslubdg.le
    syld3an2
    poslubd
    eqtrd
end
