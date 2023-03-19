include "wcel.mm"
include "wss.mm"
include "cwun.mm"
include "crnk.mm"
include "cfv.mm"
include "cr1.mm"
include "r1rankid.mm"
include "com.mm"
include "coa.mm"
include "co.mm"
include "con0.mm"
include "rankon.mm"
include "omelon.mm"
include "oacl.mm"
include "mp2an.mm"
include "c0.mm"
include "peano1.mm"
include "wb.mm"
include "oaord1.mm"
include "mpbi.mm"
include "r1ord2.mm"
include "mp2.mm"
include "sseqtr4i.mm"
include "syl6ss.mm"
include "wlim.mm"
include "wa.mm"
include "limom.mm"
include "pm3.2i.mm"
include "oalimcl.mm"
include "r1limwun.mm"
include "eqeltri.mm"
include "jctil.mm"

theorem wunex3
  let cA: class A
  let cU: class U
  let cV: class V
  let vu: setvar u
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume wunex3.u: |- U = ( R1 ` ( ( rank ` A ) +o _om ) )


  assert |- ( A e. V -> ( U e. WUni /\ A C_ U ) )

  proof
    cA
    cV
    wcel
    #
    cA
    cU
    wss
    cU
    cwun
    wcel
    @0
    cA
    cA
    crnk
    cfv
    #
    cr1
    cfv
    #
    cU
    cA
    cV
    r1rankid
    @2
    @1
    com
    coa
    co
    #
    cr1
    cfv
    #
    cU
    @3
    con0
    wcel
    #
    @1
    @3
    wcel
    #
    @2
    @4
    wss
    @1
    con0
    wcel
    #
    com
    con0
    wcel
    #
    @5
    cA
    rankon
    #
    omelon
    @1
    com
    oacl
    mp2an
    #
    c0
    com
    wcel
    #
    @6
    peano1
    @7
    @8
    @11
    @6
    wb
    @9
    omelon
    @1
    com
    oaord1
    mp2an
    mpbi
    @1
    @3
    r1ord2
    mp2
    wunex3.u
    sseqtr4i
    syl6ss
    cU
    @4
    cwun
    wunex3.u
    @5
    @3
    wlim
    #
    @4
    cwun
    wcel
    @10
    @7
    @8
    com
    wlim
    #
    wa
    @12
    @9
    @8
    @13
    omelon
    limom
    pm3.2i
    @1
    com
    con0
    oalimcl
    mp2an
    @3
    con0
    r1limwun
    mp2an
    eqeltri
    jctil
end
