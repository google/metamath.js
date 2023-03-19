include "wcel.mm"
include "co.mm"
include "c1st.mm"
include "cfv.mm"
include "c2nd.mm"
include "cxp.mm"
include "wceq.mm"
include "cv.mm"
include "wa.mm"
include "simpl.mm"
include "fveq2d.mm"
include "simpr.mm"
include "oveq12d.mm"
include "xpeq12d.mm"
include "xpchomfval.mm"
include "ovex.mm"
include "xpex.mm"
include "ovmpt2a.mm"
include "syl2anc.mm"

theorem xpchom
  let wph: wff ph
  let cB: class B
  let cC: class C
  let cD: class D
  let cT: class T
  let cH: class H
  let cJ: class J
  let cK: class K
  let cX: class X
  let cY: class Y
  let vf: setvar f
  let vg: setvar g
  let vu: setvar u
  let vv: setvar v
  let vx: setvar x
  let vy: setvar y
  assume xpchomfval.t: |- T = ( C Xc. D )
  assume xpchomfval.y: |- B = ( Base ` T )
  assume xpchomfval.h: |- H = ( Hom ` C )
  assume xpchomfval.j: |- J = ( Hom ` D )
  assume xpchomfval.k: |- K = ( Hom ` T )
  assume xpchom.x: |- ( ph -> X e. B )
  assume xpchom.y: |- ( ph -> Y e. B )


  assert |- ( ph -> ( X K Y ) = ( ( ( 1st ` X ) H ( 1st ` Y ) ) X. ( ( 2nd ` X ) J ( 2nd ` Y ) ) ) )

  proof
    wph
    cX
    cB
    wcel
    cY
    cB
    wcel
    cX
    cY
    cK
    co
    cX
    c1st
    cfv
    #
    cY
    c1st
    cfv
    #
    cH
    co
    #
    cX
    c2nd
    cfv
    #
    cY
    c2nd
    cfv
    #
    cJ
    co
    #
    cxp
    #
    wceq
    xpchom.x
    xpchom.y
    vu
    vv
    cX
    cY
    cB
    cB
    vu
    cv
    #
    c1st
    cfv
    #
    vv
    cv
    #
    c1st
    cfv
    #
    cH
    co
    #
    @7
    c2nd
    cfv
    #
    @9
    c2nd
    cfv
    #
    cJ
    co
    #
    cxp
    @6
    cK
    @7
    cX
    wceq
    #
    @9
    cY
    wceq
    #
    wa
    #
    @11
    @2
    @14
    @5
    @17
    @8
    @0
    @10
    @1
    cH
    @17
    @7
    cX
    c1st
    @15
    @16
    simpl
    #
    fveq2d
    @17
    @9
    cY
    c1st
    @15
    @16
    simpr
    #
    fveq2d
    oveq12d
    @17
    @12
    @3
    @13
    @4
    cJ
    @17
    @7
    cX
    c2nd
    @18
    fveq2d
    @17
    @9
    cY
    c2nd
    @19
    fveq2d
    oveq12d
    xpeq12d
    vv
    vu
    cB
    cC
    cD
    cT
    cH
    cJ
    cK
    xpchomfval.t
    xpchomfval.y
    xpchomfval.h
    xpchomfval.j
    xpchomfval.k
    xpchomfval
    @2
    @5
    @0
    @1
    cH
    ovex
    @3
    @4
    cJ
    ovex
    xpex
    ovmpt2a
    syl2anc
end
