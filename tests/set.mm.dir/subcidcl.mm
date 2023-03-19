include "wcel.mm"
include "cv.mm"
include "cfv.mm"
include "co.mm"
include "wral.mm"
include "cop.mm"
include "cco.mm"
include "wa.mm"
include "chomf.mm"
include "cssc.mm"
include "wbr.mm"
include "csubc.mm"
include "eqid.mm"
include "ccat.mm"
include "subcrcl.mm"
include "syl.mm"
include "issubc2.mm"
include "mpbid.mm"
include "simprd.mm"
include "simpl.mm"
include "ralimi.mm"
include "wceq.mm"
include "fveq2.mm"
include "id.mm"
include "oveq12d.mm"
include "eleq12d.mm"
include "rspcv.mm"
include "sylc.mm"

theorem subcidcl
  let wph: wff ph
  let cC: class C
  let cS: class S
  let c.1: class .1.
  let cJ: class J
  let cX: class X
  let vf: setvar f
  let vg: setvar g
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let cF: class F
  let cG: class G
  let cY: class Y
  let c.x: class .x.
  let cZ: class Z
  assume subcidcl.j: |- ( ph -> J e. ( Subcat ` C ) )
  assume subcidcl.2: |- ( ph -> J Fn ( S X. S ) )
  assume subcidcl.x: |- ( ph -> X e. S )
  assume subcidcl.1: |- .1. = ( Id ` C )


  assert |- ( ph -> ( .1. ` X ) e. ( X J X ) )

  proof
    wph
    cX
    cS
    wcel
    vx
    cv
    #
    c.1
    cfv
    #
    @0
    @0
    cJ
    co
    #
    wcel
    #
    vx
    cS
    wral
    #
    cX
    c.1
    cfv
    #
    cX
    cX
    cJ
    co
    #
    wcel
    #
    subcidcl.x
    wph
    @3
    vg
    cv
    vf
    cv
    @0
    vy
    cv
    #
    cop
    vz
    cv
    #
    cC
    cco
    cfv
    #
    co
    co
    @0
    @9
    cJ
    co
    wcel
    vg
    @8
    @9
    cJ
    co
    wral
    vf
    @0
    @8
    cJ
    co
    wral
    vz
    cS
    wral
    vy
    cS
    wral
    #
    wa
    #
    vx
    cS
    wral
    #
    @4
    wph
    cJ
    cC
    chomf
    cfv
    #
    cssc
    wbr
    #
    @13
    wph
    cJ
    cC
    csubc
    cfv
    wcel
    #
    @15
    @13
    wa
    subcidcl.j
    wph
    vx
    vy
    vz
    cC
    cS
    @10
    c.1
    vf
    vg
    @14
    cJ
    @14
    eqid
    subcidcl.1
    @10
    eqid
    wph
    @16
    cC
    ccat
    wcel
    subcidcl.j
    cC
    cJ
    subcrcl
    syl
    subcidcl.2
    issubc2
    mpbid
    simprd
    @12
    @3
    vx
    cS
    @3
    @11
    simpl
    ralimi
    syl
    @3
    @7
    vx
    cX
    cS
    @0
    cX
    wceq
    #
    @1
    @5
    @2
    @6
    @0
    cX
    c.1
    fveq2
    @17
    @0
    cX
    @0
    cX
    cJ
    @17
    id
    #
    @18
    oveq12d
    eleq12d
    rspcv
    sylc
end
