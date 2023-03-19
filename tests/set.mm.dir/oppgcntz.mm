include "cfv.mm"
include "ccntz.mm"
include "cbs.mm"
include "wss.mm"
include "cv.mm"
include "wcel.mm"
include "cplusg.mm"
include "co.mm"
include "wceq.mm"
include "wral.mm"
include "wa.mm"
include "eqcom.mm"
include "eqid.mm"
include "oppgplus.mm"
include "eqeq12i.mm"
include "bitr4i.mm"
include "ralbii.mm"
include "anbi2i.mm"
include "cvv.mm"
include "cntzrcl.mm"
include "simprd.mm"
include "elcntz.mm"
include "biadan2.mm"
include "oppgbas.mm"
include "3bitr4i.mm"
include "eqriv.mm"

theorem oppgcntz
  let cA: class A
  let cG: class G
  let cO: class O
  let cZ: class Z
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume oppggic.o: |- O = ( oppG ` G )
  assume oppgcntz.z: |- Z = ( Cntz ` G )


  assert |- ( Z ` A ) = ( ( Cntz ` O ) ` A )

  proof
    vx
    cA
    cZ
    cfv
    #
    cA
    cO
    ccntz
    cfv
    #
    cfv
    #
    cA
    cG
    cbs
    cfv
    #
    wss
    #
    vx
    cv
    #
    @3
    wcel
    #
    @5
    vy
    cv
    #
    cG
    cplusg
    cfv
    #
    co
    #
    @7
    @5
    @8
    co
    #
    wceq
    #
    vy
    cA
    wral
    #
    wa
    #
    wa
    @4
    @6
    @5
    @7
    cO
    cplusg
    cfv
    #
    co
    #
    @7
    @5
    @14
    co
    #
    wceq
    #
    vy
    cA
    wral
    #
    wa
    #
    wa
    @5
    @0
    wcel
    #
    @5
    @2
    wcel
    #
    @13
    @19
    @4
    @12
    @18
    @6
    @11
    @17
    vy
    cA
    @11
    @10
    @9
    wceq
    @17
    @9
    @10
    eqcom
    @15
    @10
    @16
    @9
    @8
    @14
    cG
    cO
    @5
    @7
    @8
    eqid
    #
    oppggic.o
    @14
    eqid
    #
    oppgplus
    @8
    @14
    cG
    cO
    @7
    @5
    @22
    oppggic.o
    @23
    oppgplus
    eqeq12i
    bitr4i
    ralbii
    anbi2i
    anbi2i
    @20
    @4
    @13
    @20
    cG
    cvv
    wcel
    @4
    @3
    cA
    cG
    @5
    cZ
    @3
    eqid
    #
    oppgcntz.z
    cntzrcl
    simprd
    vy
    @5
    @3
    @8
    cA
    cG
    cZ
    @24
    @22
    oppgcntz.z
    elcntz
    biadan2
    @21
    @4
    @19
    @21
    cO
    cvv
    wcel
    @4
    @3
    cA
    cO
    @5
    @1
    @3
    cG
    cO
    oppggic.o
    @24
    oppgbas
    #
    @1
    eqid
    #
    cntzrcl
    simprd
    vy
    @5
    @3
    @14
    cA
    cO
    @1
    @25
    @23
    @26
    elcntz
    biadan2
    3bitr4i
    eqriv
end
