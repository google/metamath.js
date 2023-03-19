include "ccrg.mm"
include "wcel.mm"
include "clidl.mm"
include "cfv.mm"
include "wceq.mm"
include "crsp.mm"
include "cbs.mm"
include "cvv.mm"
include "eqidd.mm"
include "eqid.mm"
include "opprbas.mm"
include "a1i.mm"
include "wss.mm"
include "ssv.mm"
include "cv.mm"
include "cplusg.mm"
include "co.mm"
include "wa.mm"
include "oppradd.mm"
include "oveqi.mm"
include "cmulr.mm"
include "ovexd.mm"
include "crngoppr.mm"
include "3expb.mm"
include "lidlrsppropd.mm"
include "simpld.mm"
include "syl5eq.mm"

theorem crngridl
  let cR: class R
  let cI: class I
  let cO: class O
  let vx: setvar x
  let vy: setvar y
  assume crng2idl.i: |- I = ( LIdeal ` R )
  assume crngridl.o: |- O = ( oppR ` R )


  assert |- ( R e. CRing -> I = ( LIdeal ` O ) )

  proof
    cR
    ccrg
    wcel
    #
    cI
    cR
    clidl
    cfv
    #
    cO
    clidl
    cfv
    #
    crng2idl.i
    @0
    @1
    @2
    wceq
    cR
    crsp
    cfv
    cO
    crsp
    cfv
    wceq
    @0
    vx
    vy
    cR
    cbs
    cfv
    #
    cR
    cO
    cvv
    @0
    @3
    eqidd
    @3
    cO
    cbs
    cfv
    wceq
    @0
    @3
    cR
    cO
    crngridl.o
    @3
    eqid
    #
    opprbas
    a1i
    @3
    cvv
    wss
    @0
    @3
    ssv
    a1i
    vx
    cv
    #
    vy
    cv
    #
    cR
    cplusg
    cfv
    #
    co
    @5
    @6
    cO
    cplusg
    cfv
    #
    co
    wceq
    @0
    @5
    cvv
    wcel
    @6
    cvv
    wcel
    wa
    wa
    @7
    @8
    @5
    @6
    @7
    cR
    cO
    crngridl.o
    @7
    eqid
    oppradd
    oveqi
    a1i
    @0
    @5
    @3
    wcel
    #
    @6
    @3
    wcel
    #
    wa
    wa
    @5
    @6
    cR
    cmulr
    cfv
    #
    ovexd
    @0
    @9
    @10
    @5
    @6
    @11
    co
    @5
    @6
    cO
    cmulr
    cfv
    #
    co
    wceq
    @3
    cR
    @12
    @11
    cO
    @5
    @6
    @4
    @11
    eqid
    crngridl.o
    @12
    eqid
    crngoppr
    3expb
    lidlrsppropd
    simpld
    syl5eq
end
