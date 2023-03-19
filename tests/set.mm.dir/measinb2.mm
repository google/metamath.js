include "cmeas.mm"
include "cfv.mm"
include "wcel.mm"
include "wa.mm"
include "cpw.mm"
include "cin.mm"
include "cv.mm"
include "cmpt.mm"
include "cres.mm"
include "resmpt3.mm"
include "inin.mm"
include "eqid.mm"
include "mpteq12i.mm"
include "eqtri.mm"
include "csiga.mm"
include "crn.mm"
include "cuni.mm"
include "wss.mm"
include "measinb.mm"
include "measbase.mm"
include "sigainb.mm"
include "elrnsiga.mm"
include "syl.mm"
include "sylan.mm"
include "inss1.mm"
include "a1i.mm"
include "measres.mm"
include "syl3anc.mm"
include "syl5eqelr.mm"

theorem measinb2
  let vx: setvar x
  let cA: class A
  let cS: class S
  let cM: class M

  disjoint A x
  disjoint S x
  disjoint M x
  assert |- ( ( M e. ( measures ` S ) /\ A e. S ) -> ( x e. ( S i^i ~P A ) |-> ( M ` ( x i^i A ) ) ) e. ( measures ` ( S i^i ~P A ) ) )

  proof
    cM
    cS
    cmeas
    cfv
    #
    wcel
    #
    cA
    cS
    wcel
    #
    wa
    #
    vx
    cS
    cA
    cpw
    #
    cin
    #
    vx
    cv
    cA
    cin
    cM
    cfv
    #
    cmpt
    #
    vx
    cS
    @6
    cmpt
    #
    @5
    cres
    #
    @5
    cmeas
    cfv
    #
    @9
    vx
    cS
    @5
    cin
    #
    @6
    cmpt
    @7
    vx
    cS
    @5
    @6
    resmpt3
    vx
    @11
    @6
    @5
    @6
    cS
    @4
    inin
    @6
    eqid
    mpteq12i
    eqtri
    @3
    @8
    @0
    wcel
    @5
    csiga
    crn
    cuni
    #
    wcel
    #
    @5
    cS
    wss
    #
    @9
    @10
    wcel
    vx
    cA
    cS
    cM
    measinb
    @1
    cS
    @12
    wcel
    #
    @2
    @13
    cS
    cM
    measbase
    @15
    @2
    wa
    @5
    cA
    csiga
    cfv
    wcel
    @13
    cA
    cS
    sigainb
    @5
    cA
    elrnsiga
    syl
    sylan
    @14
    @3
    cS
    @4
    inss1
    a1i
    cS
    @5
    @8
    measres
    syl3anc
    syl5eqelr
end
