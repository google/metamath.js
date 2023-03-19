include "wcel.mm"
include "cxnn0.mm"
include "w3a.mm"
include "cewlks.mm"
include "co.mm"
include "cv.mm"
include "cdm.mm"
include "cword.mm"
include "c1.mm"
include "cmin.mm"
include "cfv.mm"
include "cin.mm"
include "chash.mm"
include "cle.mm"
include "wbr.mm"
include "cfzo.mm"
include "wral.mm"
include "wa.mm"
include "cab.mm"
include "wceq.mm"
include "ewlksfval.mm"
include "3adant3.mm"
include "eleq2d.mm"
include "wb.mm"
include "eleq1.mm"
include "fveq2.mm"
include "oveq2d.mm"
include "fveq1.mm"
include "fveq2d.mm"
include "ineq12d.mm"
include "breq2d.mm"
include "raleqbidv.mm"
include "anbi12d.mm"
include "elabg.mm"
include "3ad2ant3.mm"
include "bitrd.mm"

theorem isewlk
  let cS: class S
  let cU: class U
  let vk: setvar k
  let cF: class F
  let cG: class G
  let cI: class I
  let cW: class W
  let vf: setvar f
  let vg: setvar g
  let vi: setvar i
  let vs: setvar s
  assume ewlksfval.i: |- I = ( iEdg ` G )

  disjoint G k
  disjoint S k
  disjoint W k
  disjoint F k
  disjoint G f
  disjoint G g
  disjoint G i
  disjoint G s
  disjoint f g
  disjoint f i
  disjoint f k
  disjoint f s
  disjoint g i
  disjoint g k
  disjoint g s
  disjoint i k
  disjoint i s
  disjoint k s
  disjoint S f
  disjoint S g
  disjoint S i
  disjoint S s
  disjoint W f
  disjoint W g
  disjoint W s
  disjoint F f
  disjoint I f
  assert |- ( ( G e. W /\ S e. NN0* /\ F e. U ) -> ( F e. ( G EdgWalks S ) <-> ( F e. Word dom I /\ A. k e. ( 1 ..^ ( # ` F ) ) S <_ ( # ` ( ( I ` ( F ` ( k - 1 ) ) ) i^i ( I ` ( F ` k ) ) ) ) ) ) )

  proof
    cG
    cW
    wcel
    #
    cS
    cxnn0
    wcel
    #
    cF
    cU
    wcel
    #
    w3a
    #
    cF
    cG
    cS
    cewlks
    co
    #
    wcel
    cF
    vf
    cv
    #
    cI
    cdm
    cword
    #
    wcel
    #
    cS
    vk
    cv
    #
    c1
    cmin
    co
    #
    @5
    cfv
    #
    cI
    cfv
    #
    @8
    @5
    cfv
    #
    cI
    cfv
    #
    cin
    #
    chash
    cfv
    #
    cle
    wbr
    #
    vk
    c1
    @5
    chash
    cfv
    #
    cfzo
    co
    #
    wral
    #
    wa
    #
    vf
    cab
    #
    wcel
    #
    cF
    @6
    wcel
    #
    cS
    @9
    cF
    cfv
    #
    cI
    cfv
    #
    @8
    cF
    cfv
    #
    cI
    cfv
    #
    cin
    #
    chash
    cfv
    #
    cle
    wbr
    #
    vk
    c1
    cF
    chash
    cfv
    #
    cfzo
    co
    #
    wral
    #
    wa
    #
    @3
    @4
    @21
    cF
    @0
    @1
    @4
    @21
    wceq
    @2
    cS
    vf
    vk
    cG
    cI
    cW
    ewlksfval.i
    ewlksfval
    3adant3
    eleq2d
    @2
    @0
    @22
    @34
    wb
    @1
    @20
    @34
    vf
    cF
    cU
    @5
    cF
    wceq
    #
    @7
    @23
    @19
    @33
    @5
    cF
    @6
    eleq1
    @35
    @16
    @30
    vk
    @18
    @32
    @35
    @17
    @31
    c1
    cfzo
    @5
    cF
    chash
    fveq2
    oveq2d
    @35
    @15
    @29
    cS
    cle
    @35
    @14
    @28
    chash
    @35
    @11
    @25
    @13
    @27
    @35
    @10
    @24
    cI
    @9
    @5
    cF
    fveq1
    fveq2d
    @35
    @12
    @26
    cI
    @8
    @5
    cF
    fveq1
    fveq2d
    ineq12d
    fveq2d
    breq2d
    raleqbidv
    anbi12d
    elabg
    3ad2ant3
    bitrd
end
