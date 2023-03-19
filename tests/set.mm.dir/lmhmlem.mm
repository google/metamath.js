include "clmhm.mm"
include "co.mm"
include "wcel.mm"
include "clmod.mm"
include "wa.mm"
include "cghm.mm"
include "wceq.mm"
include "cv.mm"
include "cvsca.mm"
include "cfv.mm"
include "cbs.mm"
include "wral.mm"
include "w3a.mm"
include "eqid.mm"
include "islmhm.mm"
include "3simpa.mm"
include "anim2i.mm"
include "sylbi.mm"

theorem lmhmlem
  let cS: class S
  let cT: class T
  let cF: class F
  let cK: class K
  let cL: class L
  let va: setvar a
  let vb: setvar b
  assume lmhmlem.k: |- K = ( Scalar ` S )
  assume lmhmlem.l: |- L = ( Scalar ` T )


  assert |- ( F e. ( S LMHom T ) -> ( ( S e. LMod /\ T e. LMod ) /\ ( F e. ( S GrpHom T ) /\ L = K ) ) )

  proof
    cF
    cS
    cT
    clmhm
    co
    wcel
    cS
    clmod
    wcel
    cT
    clmod
    wcel
    wa
    #
    cF
    cS
    cT
    cghm
    co
    wcel
    #
    cL
    cK
    wceq
    #
    va
    cv
    #
    vb
    cv
    #
    cS
    cvsca
    cfv
    #
    co
    cF
    cfv
    @3
    @4
    cF
    cfv
    cT
    cvsca
    cfv
    #
    co
    wceq
    vb
    cS
    cbs
    cfv
    #
    wral
    va
    cK
    cbs
    cfv
    #
    wral
    #
    w3a
    #
    wa
    @0
    @1
    @2
    wa
    #
    wa
    va
    vb
    @8
    cS
    cT
    @5
    @6
    @7
    cF
    cK
    cL
    lmhmlem.k
    lmhmlem.l
    @8
    eqid
    @7
    eqid
    @5
    eqid
    @6
    eqid
    islmhm
    @10
    @11
    @0
    @1
    @2
    @9
    3simpa
    anim2i
    sylbi
end
