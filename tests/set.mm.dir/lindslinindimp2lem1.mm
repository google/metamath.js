include "wcel.mm"
include "clmod.mm"
include "wa.mm"
include "cbs.mm"
include "cfv.mm"
include "wss.mm"
include "cv.mm"
include "cmap.mm"
include "co.mm"
include "w3a.mm"
include "cminusg.mm"
include "cgrp.mm"
include "lmodfgrp.mm"
include "adantl.mm"
include "wf.mm"
include "wi.mm"
include "elmapi.mm"
include "ffvelrn.mm"
include "a1d.mm"
include "ex.mm"
include "syl.mm"
include "com13.mm"
include "3imp.mm"
include "eqid.mm"
include "grpinvcl.mm"
include "syl2an.mm"
include "syl5eqel.mm"

theorem lindslinindimp2lem1
  let vx: setvar x
  let cB: class B
  let cR: class R
  let cS: class S
  let vf: setvar f
  let cG: class G
  let cM: class M
  let cV: class V
  let cY: class Y
  let c.0: class .0.
  let cZ: class Z
  let vg: setvar g
  let vs: setvar s
  let vy: setvar y
  let vz: setvar z
  let vk: setvar k
  assume lindslinind.r: |- R = ( Scalar ` M )
  assume lindslinind.b: |- B = ( Base ` R )
  assume lindslinind.0: |- .0. = ( 0g ` R )
  assume lindslinind.z: |- Z = ( 0g ` M )
  assume lindslinind.y: |- Y = ( ( invg ` R ) ` ( f ` x ) )
  assume lindslinind.g: |- G = ( f |` ( S \ { x } ) )

  disjoint B f
  disjoint M f
  disjoint R f
  disjoint R x
  disjoint f x
  disjoint S f
  disjoint S x
  disjoint Z f
  disjoint .0. f
  disjoint .0. x
  disjoint B g
  disjoint B s
  disjoint B y
  disjoint B z
  disjoint f g
  disjoint f s
  disjoint f y
  disjoint f z
  disjoint g s
  disjoint g y
  disjoint g z
  disjoint s y
  disjoint s z
  disjoint y z
  disjoint M g
  disjoint M s
  disjoint M y
  disjoint M z
  disjoint R z
  disjoint x z
  disjoint S g
  disjoint S s
  disjoint S y
  disjoint S z
  disjoint g x
  disjoint s x
  disjoint x y
  disjoint V g
  disjoint V s
  disjoint V y
  disjoint V z
  disjoint Z g
  disjoint Z s
  disjoint Z y
  disjoint .0. g
  disjoint .0. s
  disjoint .0. y
  disjoint .0. z
  disjoint k x
  assert |- ( ( ( S e. V /\ M e. LMod ) /\ ( S C_ ( Base ` M ) /\ x e. S /\ f e. ( B ^m S ) ) ) -> Y e. B )

  proof
    cS
    cV
    wcel
    #
    cM
    clmod
    wcel
    #
    wa
    #
    cS
    cM
    cbs
    cfv
    wss
    #
    vx
    cv
    #
    cS
    wcel
    #
    vf
    cv
    #
    cB
    cS
    cmap
    co
    wcel
    #
    w3a
    #
    wa
    cY
    @4
    @6
    cfv
    #
    cR
    cminusg
    cfv
    #
    cfv
    #
    cB
    lindslinind.y
    @2
    cR
    cgrp
    wcel
    #
    @9
    cB
    wcel
    #
    @11
    cB
    wcel
    @8
    @1
    @12
    @0
    cR
    cM
    lindslinind.r
    lmodfgrp
    adantl
    @3
    @5
    @7
    @13
    @7
    @5
    @3
    @13
    @7
    cS
    cB
    @6
    wf
    #
    @5
    @3
    @13
    wi
    #
    wi
    @6
    cB
    cS
    elmapi
    @14
    @5
    @15
    @14
    @5
    wa
    @13
    @3
    cS
    cB
    @4
    @6
    ffvelrn
    a1d
    ex
    syl
    com13
    3imp
    cB
    cR
    @10
    @9
    lindslinind.b
    @10
    eqid
    grpinvcl
    syl2an
    syl5eqel
end
