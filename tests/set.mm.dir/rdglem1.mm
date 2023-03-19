include "cv.mm"
include "wfn.mm"
include "cfv.mm"
include "cres.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "con0.mm"
include "wrex.mm"
include "cab.mm"
include "eqid.mm"
include "tfrlem3.mm"
include "fveq2.mm"
include "reseq2.mm"
include "fveq2d.mm"
include "eqeq12d.mm"
include "cbvralv.mm"
include "anbi2i.mm"
include "rexbii.mm"
include "abbii.mm"
include "eqtri.mm"

theorem rdglem1
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  let vw: setvar w
  let vf: setvar f
  let vg: setvar g
  let cG: class G
  let vv: setvar v

  disjoint x y
  disjoint f x
  disjoint g x
  disjoint f y
  disjoint g y
  disjoint f g
  disjoint x z
  disjoint y z
  disjoint g z
  disjoint f z
  disjoint G f
  disjoint G g
  disjoint G x
  disjoint G z
  disjoint w y
  disjoint G y
  disjoint w z
  disjoint g w
  disjoint G w
  disjoint v x
  disjoint v y
  disjoint f v
  disjoint g v
  disjoint v z
  disjoint v w
  disjoint G v
  assert |- { f | E. x e. On ( f Fn x /\ A. y e. x ( f ` y ) = ( G ` ( f |` y ) ) ) } = { g | E. z e. On ( g Fn z /\ A. w e. z ( g ` w ) = ( G ` ( g |` w ) ) ) }

  proof
    vf
    cv
    #
    vx
    cv
    #
    wfn
    vy
    cv
    #
    @0
    cfv
    @0
    @2
    cres
    cG
    cfv
    wceq
    vy
    @1
    wral
    wa
    vx
    con0
    wrex
    vf
    cab
    #
    vg
    cv
    #
    vz
    cv
    #
    wfn
    #
    vv
    cv
    #
    @4
    cfv
    #
    @4
    @7
    cres
    #
    cG
    cfv
    #
    wceq
    #
    vv
    @5
    wral
    #
    wa
    #
    vz
    con0
    wrex
    #
    vg
    cab
    @6
    vw
    cv
    #
    @4
    cfv
    #
    @4
    @15
    cres
    #
    cG
    cfv
    #
    wceq
    #
    vw
    @5
    wral
    #
    wa
    #
    vz
    con0
    wrex
    #
    vg
    cab
    vx
    vy
    vz
    vv
    @3
    vf
    vg
    cG
    @3
    eqid
    tfrlem3
    @14
    @22
    vg
    @13
    @21
    vz
    con0
    @12
    @20
    @6
    @11
    @19
    vv
    vw
    @5
    @7
    @15
    wceq
    #
    @8
    @16
    @10
    @18
    @7
    @15
    @4
    fveq2
    @23
    @9
    @17
    cG
    @7
    @15
    @4
    reseq2
    fveq2d
    eqeq12d
    cbvralv
    anbi2i
    rexbii
    abbii
    eqtri
end
