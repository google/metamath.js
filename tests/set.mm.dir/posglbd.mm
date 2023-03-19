include "codu.mm"
include "cfv.mm"
include "ccnv.mm"
include "eqid.mm"
include "oduleval.mm"
include "cbs.mm"
include "odubas.mm"
include "syl6eq.mm"
include "cglb.mm"
include "club.mm"
include "cpo.mm"
include "wcel.mm"
include "wceq.mm"
include "odulub.mm"
include "syl.mm"
include "eqtrd.mm"
include "odupos.mm"
include "cv.mm"
include "wa.mm"
include "wbr.mm"
include "wb.mm"
include "cvv.mm"
include "vex.mm"
include "brcnvg.mm"
include "sylancr.mm"
include "adantr.mm"
include "mpbird.mm"
include "wral.mm"
include "w3a.mm"
include "brcnv.mm"
include "ralbii.mm"
include "syl3an3b.mm"
include "sylancl.mm"
include "3ad2ant1.mm"
include "poslubdg.mm"

theorem posglbd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cS: class S
  let cT: class T
  let cG: class G
  let cK: class K
  let c.le: class .<_
  assume posglbd.l: |- .<_ = ( le ` K )
  assume posglbd.b: |- ( ph -> B = ( Base ` K ) )
  assume posglbd.g: |- ( ph -> G = ( glb ` K ) )
  assume posglbd.k: |- ( ph -> K e. Poset )
  assume posglbd.s: |- ( ph -> S C_ B )
  assume posglbd.t: |- ( ph -> T e. B )
  assume posglbd.lb: |- ( ( ph /\ x e. S ) -> T .<_ x )
  assume posglbd.gt: |- ( ( ph /\ y e. B /\ A. x e. S y .<_ x ) -> y .<_ T )

  disjoint .<_ x
  disjoint .<_ y
  disjoint x y
  disjoint B x
  disjoint B y
  disjoint K x
  disjoint K y
  disjoint S x
  disjoint S y
  disjoint G x
  disjoint G y
  disjoint T x
  disjoint T y
  disjoint ph x
  disjoint ph y
  assert |- ( ph -> ( G ` S ) = T )

  proof
    wph
    vx
    vy
    cB
    cS
    cT
    cG
    cK
    codu
    cfv
    #
    c.le
    ccnv
    #
    @0
    c.le
    cK
    @0
    eqid
    #
    posglbd.l
    oduleval
    wph
    cB
    cK
    cbs
    cfv
    #
    @0
    cbs
    cfv
    posglbd.b
    @3
    @0
    cK
    @2
    @3
    eqid
    odubas
    syl6eq
    wph
    cG
    cK
    cglb
    cfv
    #
    @0
    club
    cfv
    #
    posglbd.g
    wph
    cK
    cpo
    wcel
    #
    @4
    @5
    wceq
    posglbd.k
    @0
    @4
    cK
    cpo
    @2
    @4
    eqid
    odulub
    syl
    eqtrd
    wph
    @6
    @0
    cpo
    wcel
    posglbd.k
    @0
    cK
    @2
    odupos
    syl
    posglbd.s
    posglbd.t
    wph
    vx
    cv
    #
    cS
    wcel
    #
    wa
    @7
    cT
    @1
    wbr
    #
    cT
    @7
    c.le
    wbr
    #
    posglbd.lb
    wph
    @9
    @10
    wb
    #
    @8
    wph
    @7
    cvv
    wcel
    cT
    cB
    wcel
    #
    @11
    vx
    vex
    #
    posglbd.t
    @7
    cT
    cvv
    cB
    c.le
    brcnvg
    sylancr
    adantr
    mpbird
    wph
    vy
    cv
    #
    cB
    wcel
    #
    @7
    @14
    @1
    wbr
    #
    vx
    cS
    wral
    #
    w3a
    cT
    @14
    @1
    wbr
    #
    @14
    cT
    c.le
    wbr
    #
    @17
    wph
    @15
    @14
    @7
    c.le
    wbr
    #
    vx
    cS
    wral
    @19
    @16
    @20
    vx
    cS
    @7
    @14
    c.le
    @13
    vy
    vex
    #
    brcnv
    ralbii
    posglbd.gt
    syl3an3b
    wph
    @15
    @18
    @19
    wb
    #
    @17
    wph
    @12
    @14
    cvv
    wcel
    @22
    posglbd.t
    @21
    cT
    @14
    cB
    cvv
    c.le
    brcnvg
    sylancl
    3ad2ant1
    mpbird
    poslubdg
end
