include "cfv.mm"
include "cv.mm"
include "wbr.mm"
include "wral.mm"
include "wi.mm"
include "wa.mm"
include "crio.mm"
include "ccla.mm"
include "biid.mm"
include "glbval.mm"
include "wceq.mm"
include "ralrimiva.mm"
include "wcel.mm"
include "3exp.mm"
include "ralrimiv.mm"
include "wreu.mm"
include "wb.mm"
include "wss.mm"
include "cdm.mm"
include "clatglbcl2.mm"
include "syl2anc.mm"
include "glbeu.mm"
include "breq1.mm"
include "ralbidv.mm"
include "breq2.mm"
include "imbi2d.mm"
include "anbi12d.mm"
include "riota2.mm"
include "mpbi2and.mm"
include "eqtrd.mm"

theorem isglbd
  let wph: wff ph
  let vx: setvar x
  let vy: setvar y
  let cB: class B
  let cS: class S
  let cG: class G
  let cH: class H
  let cK: class K
  let c.le: class .<_
  let vh: setvar h
  assume isglbd.b: |- B = ( Base ` K )
  assume isglbd.l: |- .<_ = ( le ` K )
  assume isglbd.g: |- G = ( glb ` K )
  assume isglbd.1: |- ( ( ph /\ y e. S ) -> H .<_ y )
  assume isglbd.2: |- ( ( ph /\ x e. B /\ A. y e. S x .<_ y ) -> x .<_ H )
  assume isglbd.3: |- ( ph -> K e. CLat )
  assume isglbd.4: |- ( ph -> S C_ B )
  assume isglbd.5: |- ( ph -> H e. B )

  disjoint B x
  disjoint x y
  disjoint H x
  disjoint H y
  disjoint K x
  disjoint K y
  disjoint ph x
  disjoint ph y
  disjoint S x
  disjoint S y
  disjoint .<_ h
  disjoint h x
  disjoint B h
  disjoint h y
  disjoint H h
  disjoint K h
  disjoint S h
  assert |- ( ph -> ( G ` S ) = H )

  proof
    wph
    cS
    cG
    cfv
    vh
    cv
    #
    vy
    cv
    #
    c.le
    wbr
    #
    vy
    cS
    wral
    #
    vx
    cv
    #
    @1
    c.le
    wbr
    vy
    cS
    wral
    #
    @4
    @0
    c.le
    wbr
    #
    wi
    #
    vx
    cB
    wral
    #
    wa
    #
    vh
    cB
    crio
    #
    cH
    wph
    @9
    vh
    vy
    vx
    cB
    cS
    cG
    cK
    c.le
    ccla
    isglbd.b
    isglbd.l
    isglbd.g
    @9
    biid
    #
    isglbd.3
    isglbd.4
    glbval
    wph
    cH
    @1
    c.le
    wbr
    #
    vy
    cS
    wral
    #
    @5
    @4
    cH
    c.le
    wbr
    #
    wi
    #
    vx
    cB
    wral
    #
    @10
    cH
    wceq
    #
    wph
    @12
    vy
    cS
    isglbd.1
    ralrimiva
    wph
    @15
    vx
    cB
    wph
    @4
    cB
    wcel
    @5
    @14
    isglbd.2
    3exp
    ralrimiv
    wph
    cH
    cB
    wcel
    @9
    vh
    cB
    wreu
    @13
    @16
    wa
    #
    @17
    wb
    isglbd.5
    wph
    @9
    vh
    vy
    vx
    cB
    cS
    cG
    cK
    c.le
    ccla
    isglbd.b
    isglbd.l
    isglbd.g
    @11
    isglbd.3
    wph
    cK
    ccla
    wcel
    cS
    cB
    wss
    cS
    cG
    cdm
    wcel
    isglbd.3
    isglbd.4
    cB
    cS
    cG
    cK
    isglbd.b
    isglbd.g
    clatglbcl2
    syl2anc
    glbeu
    @9
    @18
    vh
    cB
    cH
    @0
    cH
    wceq
    #
    @3
    @13
    @8
    @16
    @19
    @2
    @12
    vy
    cS
    @0
    cH
    @1
    c.le
    breq1
    ralbidv
    @19
    @7
    @15
    vx
    cB
    @19
    @6
    @14
    @5
    @0
    cH
    @4
    c.le
    breq2
    imbi2d
    ralbidv
    anbi12d
    riota2
    syl2anc
    mpbi2and
    eqtrd
end
