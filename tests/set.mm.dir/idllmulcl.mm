include "crngo.mm"
include "wcel.mm"
include "cidl.mm"
include "cfv.mm"
include "wa.mm"
include "cv.mm"
include "co.mm"
include "wral.mm"
include "wss.mm"
include "cgi.mm"
include "w3a.mm"
include "eqid.mm"
include "isidl.mm"
include "biimpa.mm"
include "simp3d.mm"
include "simpl.mm"
include "ralimi.mm"
include "adantl.mm"
include "syl.mm"
include "wceq.mm"
include "oveq2.mm"
include "eleq1d.mm"
include "oveq1.mm"
include "rspc2v.mm"
include "mpan9.mm"

theorem idllmulcl
  let cA: class A
  let cB: class B
  let cR: class R
  let cG: class G
  let cH: class H
  let cI: class I
  let cX: class X
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume idllmulcl.1: |- G = ( 1st ` R )
  assume idllmulcl.2: |- H = ( 2nd ` R )
  assume idllmulcl.3: |- X = ran G


  assert |- ( ( ( R e. RingOps /\ I e. ( Idl ` R ) ) /\ ( A e. I /\ B e. X ) ) -> ( B H A ) e. I )

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
    vz
    cv
    #
    vx
    cv
    #
    cH
    co
    #
    cI
    wcel
    #
    vz
    cX
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
    cX
    wcel
    wa
    cB
    cA
    cH
    co
    #
    cI
    wcel
    #
    @2
    @4
    vy
    cv
    cG
    co
    cI
    wcel
    vy
    cI
    wral
    #
    @6
    @4
    @3
    cH
    co
    cI
    wcel
    #
    wa
    #
    vz
    cX
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
    cX
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
    cH
    cI
    cX
    @18
    idllmulcl.1
    idllmulcl.2
    idllmulcl.3
    @18
    eqid
    isidl
    biimpa
    simp3d
    @15
    @7
    vx
    cI
    @14
    @7
    @11
    @13
    @6
    vz
    cX
    @6
    @12
    simpl
    ralimi
    adantl
    ralimi
    syl
    @6
    @10
    @3
    cA
    cH
    co
    #
    cI
    wcel
    vx
    vz
    cA
    cB
    cI
    cX
    @4
    cA
    wceq
    @5
    @20
    cI
    @4
    cA
    @3
    cH
    oveq2
    eleq1d
    @3
    cB
    wceq
    @20
    @9
    cI
    @3
    cB
    cA
    cH
    oveq1
    eleq1d
    rspc2v
    mpan9
end
