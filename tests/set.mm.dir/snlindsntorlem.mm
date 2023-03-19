include "clmod.mm"
include "wcel.mm"
include "wa.mm"
include "cv.mm"
include "csn.mm"
include "clinc.mm"
include "cfv.mm"
include "co.mm"
include "wceq.mm"
include "wi.mm"
include "cmap.mm"
include "wral.mm"
include "cop.mm"
include "wf.mm"
include "eqidd.mm"
include "wb.mm"
include "fsng.mm"
include "adantll.mm"
include "mpbird.mm"
include "wss.mm"
include "snssi.mm"
include "adantl.mm"
include "fssd.mm"
include "cvv.mm"
include "cbs.mm"
include "fvex.mm"
include "eqeltri.mm"
include "snex.mm"
include "pm3.2i.mm"
include "elmapg.mm"
include "mp1i.mm"
include "oveq1.mm"
include "eqeq1d.mm"
include "fveq1.mm"
include "imbi12d.mm"
include "lincvalsng.mm"
include "3expa.mm"
include "fvsng.mm"
include "sylan9bbr.mm"
include "rspcdv.mm"
include "ralrimdva.mm"

theorem snlindsntorlem
  let cB: class B
  let cR: class R
  let cS: class S
  let c.x: class .x.
  let vf: setvar f
  let cM: class M
  let cX: class X
  let c.0: class .0.
  let cZ: class Z
  let vs: setvar s
  let vx: setvar x
  let vy: setvar y
  let vk: setvar k
  assume snlindsntor.b: |- B = ( Base ` M )
  assume snlindsntor.r: |- R = ( Scalar ` M )
  assume snlindsntor.s: |- S = ( Base ` R )
  assume snlindsntor.0: |- .0. = ( 0g ` R )
  assume snlindsntor.z: |- Z = ( 0g ` M )
  assume snlindsntor.t: |- .x. = ( .s ` M )

  disjoint B f
  disjoint B s
  disjoint f s
  disjoint M f
  disjoint M s
  disjoint S f
  disjoint S s
  disjoint X f
  disjoint X s
  disjoint Z f
  disjoint Z s
  disjoint .x. f
  disjoint .x. s
  disjoint .0. f
  disjoint .0. s
  disjoint M x
  disjoint M y
  disjoint f x
  disjoint f y
  disjoint s x
  disjoint s y
  disjoint x y
  disjoint X x
  disjoint X y
  disjoint k x
  assert |- ( ( M e. LMod /\ X e. B ) -> ( A. f e. ( S ^m { X } ) ( ( f ( linC ` M ) { X } ) = Z -> ( f ` X ) = .0. ) -> A. s e. S ( ( s .x. X ) = Z -> s = .0. ) ) )

  proof
    cM
    clmod
    wcel
    #
    cX
    cB
    wcel
    #
    wa
    #
    vf
    cv
    #
    cX
    csn
    #
    cM
    clinc
    cfv
    #
    co
    #
    cZ
    wceq
    #
    cX
    @3
    cfv
    #
    c.0
    wceq
    #
    wi
    #
    vf
    cS
    @4
    cmap
    co
    #
    wral
    vs
    cv
    #
    cX
    c.x
    co
    #
    cZ
    wceq
    #
    @12
    c.0
    wceq
    #
    wi
    #
    vs
    cS
    @2
    @12
    cS
    wcel
    #
    wa
    #
    @10
    @16
    vf
    cX
    @12
    cop
    csn
    #
    @11
    @18
    @19
    @11
    wcel
    #
    @4
    cS
    @19
    wf
    #
    @18
    @4
    @12
    csn
    #
    cS
    @19
    @18
    @4
    @22
    @19
    wf
    #
    @19
    @19
    wceq
    #
    @18
    @19
    eqidd
    @1
    @17
    @23
    @24
    wb
    @0
    cX
    @12
    cB
    cS
    @19
    fsng
    adantll
    mpbird
    @17
    @22
    cS
    wss
    @2
    @12
    cS
    snssi
    adantl
    fssd
    cS
    cvv
    wcel
    #
    @4
    cvv
    wcel
    #
    wa
    @20
    @21
    wb
    @18
    @25
    @26
    cS
    cR
    cbs
    cfv
    cvv
    snlindsntor.s
    cR
    cbs
    fvex
    eqeltri
    cX
    snex
    pm3.2i
    cS
    @4
    @19
    cvv
    cvv
    elmapg
    mp1i
    mpbird
    @3
    @19
    wceq
    #
    @10
    @19
    @4
    @5
    co
    #
    cZ
    wceq
    #
    cX
    @19
    cfv
    #
    c.0
    wceq
    #
    wi
    @18
    @16
    @27
    @7
    @29
    @9
    @31
    @27
    @6
    @28
    cZ
    @3
    @19
    @4
    @5
    oveq1
    eqeq1d
    @27
    @8
    @30
    c.0
    cX
    @3
    @19
    fveq1
    eqeq1d
    imbi12d
    @18
    @29
    @14
    @31
    @15
    @18
    @28
    @13
    cZ
    @0
    @1
    @17
    @28
    @13
    wceq
    cB
    cS
    cR
    c.x
    cM
    cX
    @12
    snlindsntor.b
    snlindsntor.r
    snlindsntor.s
    snlindsntor.t
    lincvalsng
    3expa
    eqeq1d
    @18
    @30
    @12
    c.0
    @1
    @17
    @30
    @12
    wceq
    @0
    cX
    @12
    cB
    cS
    fvsng
    adantll
    eqeq1d
    imbi12d
    sylan9bbr
    rspcdv
    ralrimdva
end
