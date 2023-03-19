include "cgr.mm"
include "wcel.mm"
include "wa.mm"
include "cghomOLD.mm"
include "co.mm"
include "crn.mm"
include "wf.mm"
include "cv.mm"
include "cfv.mm"
include "wceq.mm"
include "wral.mm"
include "elghomlem1OLD.mm"
include "eleq2d.mm"
include "wb.mm"
include "cvv.mm"
include "elex.mm"
include "feq1.mm"
include "fveq1.mm"
include "oveq12d.mm"
include "eqeq12d.mm"
include "2ralbidv.mm"
include "anbi12d.mm"
include "elab2g.mm"
include "biimpd.mm"
include "mpcom.mm"
include "wi.mm"
include "rnexg.mm"
include "fex.mm"
include "expcom.mm"
include "syl.mm"
include "adantrd.mm"
include "biimprd.mm"
include "syli.mm"
include "impbid2.mm"
include "adantr.mm"
include "bitrd.mm"

theorem elghomlem2OLD
  let vx: setvar x
  let vy: setvar y
  let cS: class S
  let vf: setvar f
  let cF: class F
  let cG: class G
  let cH: class H
  let vg: setvar g
  let vh: setvar h
  assume elghomlem1OLD.1: |- S = { f | ( f : ran G --> ran H /\ A. x e. ran G A. y e. ran G ( ( f ` x ) H ( f ` y ) ) = ( f ` ( x G y ) ) ) }

  disjoint f x
  disjoint f y
  disjoint F f
  disjoint x y
  disjoint F x
  disjoint F y
  disjoint G f
  disjoint G x
  disjoint G y
  disjoint H f
  disjoint H x
  disjoint H y
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
  assert |- ( ( G e. GrpOp /\ H e. GrpOp ) -> ( F e. ( G GrpOpHom H ) <-> ( F : ran G --> ran H /\ A. x e. ran G A. y e. ran G ( ( F ` x ) H ( F ` y ) ) = ( F ` ( x G y ) ) ) ) )

  proof
    cG
    cgr
    wcel
    #
    cH
    cgr
    wcel
    #
    wa
    #
    cF
    cG
    cH
    cghomOLD
    co
    #
    wcel
    cF
    cS
    wcel
    #
    cG
    crn
    #
    cH
    crn
    #
    cF
    wf
    #
    vx
    cv
    #
    cF
    cfv
    #
    vy
    cv
    #
    cF
    cfv
    #
    cH
    co
    #
    @8
    @10
    cG
    co
    #
    cF
    cfv
    #
    wceq
    #
    vy
    @5
    wral
    vx
    @5
    wral
    #
    wa
    #
    @2
    @3
    cS
    cF
    vx
    vy
    cS
    vf
    cG
    cH
    elghomlem1OLD.1
    elghomlem1OLD
    eleq2d
    @0
    @4
    @17
    wb
    @1
    @0
    @4
    @17
    cF
    cvv
    wcel
    #
    @4
    @17
    cF
    cS
    elex
    @18
    @4
    @17
    @5
    @6
    vf
    cv
    #
    wf
    #
    @8
    @19
    cfv
    #
    @10
    @19
    cfv
    #
    cH
    co
    #
    @13
    @19
    cfv
    #
    wceq
    #
    vy
    @5
    wral
    vx
    @5
    wral
    #
    wa
    @17
    vf
    cF
    cS
    cvv
    @19
    cF
    wceq
    #
    @20
    @7
    @26
    @16
    @5
    @6
    @19
    cF
    feq1
    @27
    @25
    @15
    vx
    vy
    @5
    @5
    @27
    @23
    @12
    @24
    @14
    @27
    @21
    @9
    @22
    @11
    cH
    @8
    @19
    cF
    fveq1
    @10
    @19
    cF
    fveq1
    oveq12d
    @13
    @19
    cF
    fveq1
    eqeq12d
    2ralbidv
    anbi12d
    elghomlem1OLD.1
    elab2g
    #
    biimpd
    mpcom
    @17
    @0
    @18
    @4
    @0
    @7
    @18
    @16
    @0
    @5
    cvv
    wcel
    #
    @7
    @18
    wi
    cG
    cgr
    rnexg
    @7
    @29
    @18
    @5
    @6
    cvv
    cF
    fex
    expcom
    syl
    adantrd
    @18
    @4
    @17
    @28
    biimprd
    syli
    impbid2
    adantr
    bitrd
end
