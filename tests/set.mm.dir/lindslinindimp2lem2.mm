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
include "csn.mm"
include "cdif.mm"
include "wf.mm"
include "cres.mm"
include "elmapi.mm"
include "3ad2ant3.mm"
include "adantl.mm"
include "difss.mm"
include "fssres.mm"
include "sylancl.mm"
include "feq1i.mm"
include "sylibr.mm"
include "cvv.mm"
include "wb.mm"
include "fvex.mm"
include "eqeltri.mm"
include "difexg.mm"
include "ad2antrr.mm"
include "elmapg.mm"
include "sylancr.mm"
include "mpbird.mm"

theorem lindslinindimp2lem2
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
  assert |- ( ( ( S e. V /\ M e. LMod ) /\ ( S C_ ( Base ` M ) /\ x e. S /\ f e. ( B ^m S ) ) ) -> G e. ( B ^m ( S \ { x } ) ) )

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
    #
    cG
    cB
    cS
    @4
    csn
    #
    cdif
    #
    cmap
    co
    wcel
    #
    @11
    cB
    cG
    wf
    #
    @9
    @11
    cB
    @6
    @11
    cres
    #
    wf
    #
    @13
    @9
    cS
    cB
    @6
    wf
    #
    @11
    cS
    wss
    @15
    @8
    @16
    @2
    @7
    @3
    @16
    @5
    @6
    cB
    cS
    elmapi
    3ad2ant3
    adantl
    cS
    @10
    difss
    cS
    cB
    @11
    @6
    fssres
    sylancl
    @11
    cB
    cG
    @14
    lindslinind.g
    feq1i
    sylibr
    @9
    cB
    cvv
    wcel
    @11
    cvv
    wcel
    #
    @12
    @13
    wb
    cB
    cR
    cbs
    cfv
    cvv
    lindslinind.b
    cR
    cbs
    fvex
    eqeltri
    @0
    @17
    @1
    @8
    cS
    @10
    cV
    difexg
    ad2antrr
    cB
    @11
    cG
    cvv
    cvv
    elmapg
    sylancr
    mpbird
end
