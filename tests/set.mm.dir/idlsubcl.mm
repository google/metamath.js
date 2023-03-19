include "crngo.mm"
include "wcel.mm"
include "cidl.mm"
include "cfv.mm"
include "wa.mm"
include "co.mm"
include "cgn.mm"
include "crn.mm"
include "wceq.mm"
include "eqid.mm"
include "idlcl.mm"
include "anim12da.mm"
include "rngosub.mm"
include "3expb.mm"
include "adantlr.mm"
include "syldan.mm"
include "simprl.mm"
include "idlnegcl.mm"
include "adantrl.mm"
include "jca.mm"
include "idladdcl.mm"
include "eqeltrd.mm"

theorem idlsubcl
  let cA: class A
  let cB: class B
  let cD: class D
  let cR: class R
  let cG: class G
  let cI: class I
  assume idlsubcl.1: |- G = ( 1st ` R )
  assume idlsubcl.2: |- D = ( /g ` G )


  assert |- ( ( ( R e. RingOps /\ I e. ( Idl ` R ) ) /\ ( A e. I /\ B e. I ) ) -> ( A D B ) e. I )

  proof
    cR
    crngo
    wcel
    #
    cI
    cR
    cidl
    cfv
    wcel
    #
    wa
    #
    cA
    cI
    wcel
    #
    cB
    cI
    wcel
    #
    wa
    #
    wa
    #
    cA
    cB
    cD
    co
    #
    cA
    cB
    cG
    cgn
    cfv
    #
    cfv
    #
    cG
    co
    #
    cI
    @2
    @5
    cA
    cG
    crn
    #
    wcel
    #
    cB
    @11
    wcel
    #
    wa
    #
    @7
    @10
    wceq
    #
    @2
    @3
    @4
    @12
    @13
    cA
    cR
    cG
    cI
    @11
    idlsubcl.1
    @11
    eqid
    #
    idlcl
    cB
    cR
    cG
    cI
    @11
    idlsubcl.1
    @16
    idlcl
    anim12da
    @0
    @14
    @15
    @1
    @0
    @12
    @13
    @15
    cA
    cB
    cD
    cR
    cG
    @8
    @11
    idlsubcl.1
    @16
    @8
    eqid
    #
    idlsubcl.2
    rngosub
    3expb
    adantlr
    syldan
    @2
    @5
    @3
    @9
    cI
    wcel
    #
    wa
    @10
    cI
    wcel
    @6
    @3
    @18
    @2
    @3
    @4
    simprl
    @2
    @4
    @18
    @3
    cB
    cR
    cG
    cI
    @8
    idlsubcl.1
    @17
    idlnegcl
    adantrl
    jca
    cA
    @9
    cR
    cG
    cI
    idlsubcl.1
    idladdcl
    syldan
    eqeltrd
end
