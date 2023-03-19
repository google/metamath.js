include "cgr.mm"
include "wcel.mm"
include "cvv.mm"
include "cghomOLD.mm"
include "co.mm"
include "wceq.mm"
include "crn.mm"
include "rnexg.mm"
include "cv.mm"
include "cfv.mm"
include "wral.mm"
include "fabexg.mm"
include "syl2an.mm"
include "wf.mm"
include "wa.mm"
include "cab.mm"
include "rneq.mm"
include "feq2d.mm"
include "oveq.mm"
include "fveq2d.mm"
include "eqeq2d.mm"
include "raleqbidv.mm"
include "anbi12d.mm"
include "abbidv.mm"
include "feq3d.mm"
include "eqeq1d.mm"
include "2ralbidv.mm"
include "syl6eqr.mm"
include "df-ghomOLD.mm"
include "ovmpt2g.mm"
include "mpd3an3.mm"

theorem elghomlem1OLD
  let vx: setvar x
  let vy: setvar y
  let cS: class S
  let vf: setvar f
  let cG: class G
  let cH: class H
  let cF: class F
  let vg: setvar g
  let vh: setvar h
  assume elghomlem1OLD.1: |- S = { f | ( f : ran G --> ran H /\ A. x e. ran G A. y e. ran G ( ( f ` x ) H ( f ` y ) ) = ( f ` ( x G y ) ) ) }

  disjoint f x
  disjoint f y
  disjoint x y
  disjoint G f
  disjoint G x
  disjoint G y
  disjoint H f
  disjoint H x
  disjoint H y
  disjoint F f
  disjoint F x
  disjoint F y
  disjoint f g
  disjoint f h
  disjoint g h
  disjoint g x
  disjoint g y
  disjoint G g
  disjoint h x
  disjoint h y
  disjoint G h
  disjoint H g
  disjoint H h
  disjoint S g
  disjoint S h
  assert |- ( ( G e. GrpOp /\ H e. GrpOp ) -> ( G GrpOpHom H ) = S )

  proof
    cG
    cgr
    wcel
    #
    cH
    cgr
    wcel
    #
    cS
    cvv
    wcel
    #
    cG
    cH
    cghomOLD
    co
    cS
    wceq
    @0
    cG
    crn
    #
    cvv
    wcel
    cH
    crn
    #
    cvv
    wcel
    @2
    @1
    cG
    cgr
    rnexg
    cH
    cgr
    rnexg
    vx
    cv
    #
    vf
    cv
    #
    cfv
    #
    vy
    cv
    #
    @6
    cfv
    #
    cH
    co
    #
    @5
    @8
    cG
    co
    #
    @6
    cfv
    #
    wceq
    #
    vy
    @3
    wral
    vx
    @3
    wral
    #
    vf
    @3
    @4
    cvv
    cvv
    cS
    elghomlem1OLD.1
    fabexg
    syl2an
    vg
    vh
    cG
    cH
    cgr
    cgr
    vg
    cv
    #
    crn
    #
    vh
    cv
    #
    crn
    #
    @6
    wf
    #
    @7
    @9
    @17
    co
    #
    @5
    @8
    @15
    co
    #
    @6
    cfv
    #
    wceq
    #
    vy
    @16
    wral
    #
    vx
    @16
    wral
    #
    wa
    #
    vf
    cab
    cS
    cghomOLD
    @3
    @18
    @6
    wf
    #
    @20
    @12
    wceq
    #
    vy
    @3
    wral
    #
    vx
    @3
    wral
    #
    wa
    #
    vf
    cab
    #
    cvv
    @15
    cG
    wceq
    #
    @26
    @31
    vf
    @33
    @19
    @27
    @25
    @30
    @33
    @16
    @3
    @18
    @6
    @15
    cG
    rneq
    #
    feq2d
    @33
    @24
    @29
    vx
    @16
    @3
    @34
    @33
    @23
    @28
    vy
    @16
    @3
    @34
    @33
    @22
    @12
    @20
    @33
    @21
    @11
    @6
    @5
    @8
    @15
    cG
    oveq
    fveq2d
    eqeq2d
    raleqbidv
    raleqbidv
    anbi12d
    abbidv
    @17
    cH
    wceq
    #
    @32
    @3
    @4
    @6
    wf
    #
    @14
    wa
    #
    vf
    cab
    cS
    @35
    @31
    @37
    vf
    @35
    @27
    @36
    @30
    @14
    @35
    @18
    @4
    @6
    @3
    @17
    cH
    rneq
    feq3d
    @35
    @28
    @13
    vx
    vy
    @3
    @3
    @35
    @20
    @10
    @12
    @7
    @9
    @17
    cH
    oveq
    eqeq1d
    2ralbidv
    anbi12d
    abbidv
    elghomlem1OLD.1
    syl6eqr
    vx
    vy
    vf
    vg
    vh
    df-ghomOLD
    ovmpt2g
    mpd3an3
end
