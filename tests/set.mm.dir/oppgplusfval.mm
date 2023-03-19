include "cplusg.mm"
include "cfv.mm"
include "ctpos.mm"
include "cvv.mm"
include "wcel.mm"
include "wceq.mm"
include "cnx.mm"
include "cop.mm"
include "csts.mm"
include "co.mm"
include "fvex.mm"
include "eqeltri.mm"
include "tposex.mm"
include "plusgid.mm"
include "setsid.mm"
include "mpan2.mm"
include "oppgval.mm"
include "fveq2i.mm"
include "syl6reqr.mm"
include "wn.mm"
include "c0.mm"
include "tpos0.mm"
include "str0.mm"
include "eqtr2i.mm"
include "reldmsets.mm"
include "ovprc1.mm"
include "syl5eq.mm"
include "fveq2d.mm"
include "fvprc.mm"
include "tposeqd.mm"
include "3eqtr4a.mm"
include "pm2.61i.mm"
include "eqtri.mm"

theorem oppgplusfval
  let c.pl: class .+
  let c.pb: class .+b
  let cR: class R
  let cO: class O
  let vx: setvar x
  let cX: class X
  let cY: class Y
  assume oppgval.2: |- .+ = ( +g ` R )
  assume oppgval.3: |- O = ( oppG ` R )
  assume oppgplusfval.4: |- .+b = ( +g ` O )


  assert |- .+b = tpos .+

  proof
    c.pb
    cO
    cplusg
    cfv
    #
    c.pl
    ctpos
    #
    oppgplusfval.4
    cR
    cvv
    wcel
    #
    @0
    @1
    wceq
    @2
    @1
    cR
    cnx
    cplusg
    cfv
    #
    @1
    cop
    #
    csts
    co
    #
    cplusg
    cfv
    #
    @0
    @2
    @1
    cvv
    wcel
    @1
    @6
    wceq
    c.pl
    c.pl
    cR
    cplusg
    cfv
    #
    cvv
    oppgval.2
    cR
    cplusg
    fvex
    eqeltri
    tposex
    cvv
    @1
    cplusg
    cvv
    cR
    plusgid
    setsid
    mpan2
    cO
    @5
    cplusg
    c.pl
    cR
    cO
    oppgval.2
    oppgval.3
    oppgval
    #
    fveq2i
    syl6reqr
    @2
    wn
    #
    c0
    cplusg
    cfv
    #
    c0
    ctpos
    #
    @0
    @1
    @11
    c0
    @10
    tpos0
    cplusg
    @3
    plusgid
    str0
    eqtr2i
    @9
    cO
    c0
    cplusg
    @9
    cO
    @5
    c0
    @8
    cR
    @4
    csts
    reldmsets
    ovprc1
    syl5eq
    fveq2d
    @9
    c.pl
    c0
    @9
    c.pl
    @7
    c0
    oppgval.2
    cR
    cplusg
    fvprc
    syl5eq
    tposeqd
    3eqtr4a
    pm2.61i
    eqtri
end
