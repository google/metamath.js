include "crngo.mm"
include "wcel.mm"
include "cidl.mm"
include "cfv.mm"
include "wa.mm"
include "cv.mm"
include "co.mm"
include "wral.mm"
include "c2nd.mm"
include "crn.mm"
include "wss.mm"
include "cgi.mm"
include "w3a.mm"
include "eqid.mm"
include "isidl.mm"
include "biimpa.mm"
include "simp3d.mm"
include "simpl.mm"
include "ralimi.mm"
include "syl.mm"
include "wceq.mm"
include "oveq1.mm"
include "eleq1d.mm"
include "oveq2.mm"
include "rspc2v.mm"
include "mpan9.mm"

theorem idladdcl
  let cA: class A
  let cB: class B
  let cR: class R
  let cG: class G
  let cI: class I
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume idladdcl.1: |- G = ( 1st ` R )


  assert |- ( ( ( R e. RingOps /\ I e. ( Idl ` R ) ) /\ ( A e. I /\ B e. I ) ) -> ( A G B ) e. I )

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
    vx
    cv
    #
    vy
    cv
    #
    cG
    co
    #
    cI
    wcel
    #
    vy
    cI
    wral
    #
    vx
    cI
    wral
    #
    cA
    cI
    wcel
    cB
    cI
    wcel
    wa
    cA
    cB
    cG
    co
    #
    cI
    wcel
    #
    @2
    @7
    vz
    cv
    #
    @3
    cR
    c2nd
    cfv
    #
    co
    cI
    wcel
    @3
    @11
    @12
    co
    cI
    wcel
    wa
    vz
    cG
    crn
    #
    wral
    #
    wa
    #
    vx
    cI
    wral
    #
    @8
    @2
    cI
    @13
    wss
    #
    cG
    cgi
    cfv
    #
    cI
    wcel
    #
    @16
    @0
    @1
    @17
    @19
    @16
    w3a
    vx
    vy
    vz
    cR
    cG
    @12
    cI
    @13
    @18
    idladdcl.1
    @12
    eqid
    @13
    eqid
    @18
    eqid
    isidl
    biimpa
    simp3d
    @15
    @7
    vx
    cI
    @7
    @14
    simpl
    ralimi
    syl
    @6
    @10
    cA
    @4
    cG
    co
    #
    cI
    wcel
    vx
    vy
    cA
    cB
    cI
    cI
    @3
    cA
    wceq
    @5
    @20
    cI
    @3
    cA
    @4
    cG
    oveq1
    eleq1d
    @4
    cB
    wceq
    @20
    @9
    cI
    @4
    cB
    cA
    cG
    oveq2
    eleq1d
    rspc2v
    mpan9
end
