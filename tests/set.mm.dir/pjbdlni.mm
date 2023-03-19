include "cpjh.mm"
include "cfv.mm"
include "cbo.mm"
include "wcel.mm"
include "clo.mm"
include "cnop.mm"
include "cr.mm"
include "pjlnopi.mm"
include "cch.mm"
include "c0h.mm"
include "wceq.mm"
include "fveq2.mm"
include "fveq2d.mm"
include "eleq1d.mm"
include "wne.mm"
include "c1.mm"
include "pjnmopi.mm"
include "1re.mm"
include "syl6eqel.mm"
include "adantl.mm"
include "cc0.mm"
include "ch0o.mm"
include "df-h0op.mm"
include "fveq2i.mm"
include "nmop0.mm"
include "eqtr3i.mm"
include "0re.mm"
include "eqeltri.mm"
include "a1i.mm"
include "pm2.61ne.mm"
include "ax-mp.mm"
include "elbdop2.mm"
include "mpbir2an.mm"

theorem pjbdlni
  let cH: class H
  let vw: setvar w
  let vx: setvar x
  let vy: setvar y
  let vz: setvar z
  assume pjhmop.1: |- H e. CH


  assert |- ( projh ` H ) e. BndLinOp

  proof
    cH
    cpjh
    cfv
    #
    cbo
    wcel
    @0
    clo
    wcel
    @0
    cnop
    cfv
    #
    cr
    wcel
    #
    cH
    pjhmop.1
    pjlnopi
    cH
    cch
    wcel
    #
    @2
    pjhmop.1
    @3
    @2
    c0h
    cpjh
    cfv
    #
    cnop
    cfv
    #
    cr
    wcel
    #
    cH
    c0h
    cH
    c0h
    wceq
    #
    @1
    @5
    cr
    @7
    @0
    @4
    cnop
    cH
    c0h
    cpjh
    fveq2
    fveq2d
    eleq1d
    cH
    c0h
    wne
    #
    @2
    @3
    @8
    @1
    c1
    cr
    cH
    pjhmop.1
    pjnmopi
    1re
    syl6eqel
    adantl
    @6
    @3
    @5
    cc0
    cr
    ch0o
    cnop
    cfv
    @5
    cc0
    ch0o
    @4
    cnop
    df-h0op
    fveq2i
    nmop0
    eqtr3i
    0re
    eqeltri
    a1i
    pm2.61ne
    ax-mp
    @0
    elbdop2
    mpbir2an
end
